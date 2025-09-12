--
-- CoeUp.lean
--
import LeanToolkit.Common

open Lean Elab Command Lean.Meta Lean.Elab.Term Lean.Meta.SynthInstance Lean.Elab.Deriving
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

namespace AR.Lang.Compose.CoeUp

/-
  Modified version of the one at
    https://github.com/leanprover/lean4/blob/f45c19b428496aa99036d317c2b8bd83dae4e7ea/src/Lean/Elab/Deriving/Repr.lean
-/
private def mkRhs
  (coeFrom coeTo: InductiveVal)
  (ctorName: Name)
  (argNames: Array Name)          -- arguments of the coeFrom type
  (fnName: Name)                  -- name of the coercion function
  (xs: Array Expr)
: TermElabM (Array (TSyntax `term) × TSyntax `term × List Binding × TSyntax `term) := do
  let mut patterns := #[]
  let mut bindings: Array Binding := #[]
  -- add `_` pattern for indices
  for _ in [:coeFrom.numIndices] do
    patterns := patterns.push (← `(_))
  let mut ctorArgs := #[]
  let mut rhs : Term := mkIdent ((coeTo.name.append ctorName.componentsRev.head!))
  let mut rhs': Term := mkIdent ((coeTo.name.append ctorName.componentsRev.head!))
  for h: i in [:xs.size] do
    -- Note: some inductive parameters are explicit if they were promoted from indices,
    -- so we process all constructor arguments in the same loop.
    let x := xs[i]
    let a ← if i < coeFrom.numParams then
              if let some y := argNames.get? i then pure y else throwError m!"{i} out of bounds in mkRhs"
            else mkFreshUserName `a
    if i < coeFrom.numParams then
      ctorArgs := ctorArgs
      -- add `_` for inductive parameters, they are inaccessible
      --ctorArgs := ctorArgs.push (← `(_))
    else
      ctorArgs := ctorArgs.push a

    let bi ← x.fvarId!.getBinderInfo
    if bi.isExplicit then
      let paramType ← inferType x
      bindings := bindings.push ⟨a, ← PrettyPrinter.delab paramType, bi⟩
      -- logInfo m!"paramType: {paramType} -- coeFrom: {coeFrom.name}"
      if paramType.constName == coeFrom.name || paramType.isAppOf coeFrom.name then
        rhs ← `($rhs ($(mkIdent fnName) $(mkIdent a):ident))
        -- logInfo m!"paramType match!!!  {rhs}"
      else if (← isType x <||> isProof x) then
        rhs ← `($rhs "_")
      else
        rhs ← `($rhs $(mkIdent a))

  let ctorArgs' := ctorArgs.map mkIdent
  patterns := patterns.push (← `($(mkIdent ctorName):ident $ctorArgs':term*))
  rhs' ← `($rhs' $ctorArgs':term*)
  return ⟨patterns, rhs', bindings.toList, rhs⟩

private def mkBody
  (coeFrom coeTo: InductiveVal)
  (auxFunName: Name)
  (paramName: Ident)
: TermElabM (Term × Array Command) := do
  let ⟨alts, cmds⟩ ← mkAlts
  let t ← `(match $paramName:ident with $alts:matchAlt*)
  return ⟨t, cmds⟩
where
  mkAlts: TermElabM (Array (TSyntax ``matchAlt) × Array Command) := do
    let mut alts := #[]
    let mut cmds := #[]
    let argNames      ← mkInductArgNames coeFrom
    for ctorName in coeFrom.ctors do
      let ctorInfo ← getConstInfoCtor ctorName

      let ⟨patterns, _, _, rhs⟩ ← forallTelescopeReducing ctorInfo.type λ xs _ => do
        mkRhs coeFrom coeTo ctorName argNames auxFunName xs

      let alt ← `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt

      --let downCast ← `(instance $bs:bracketedBinder* : CoeDep $f $rhs' $t where
      --                  coe := $(patterns[0]!)
      --                )
      --cmds := cmds.push downCast
    return ⟨alts, cmds⟩

private def mkAuxFunction
  (auxFunName : Name)
  (coeFrom coeTo: InductiveVal)
: TermElabM (Command × Array Command) := do
  let ⟨ps, _⟩ ← toParams coeFrom.type #[]
  let paramName ← mkFreshUserName `x
  let paramType' ← `($(mkIdent coeFrom.name))
  let paramType ← mkInstantiatedType paramType' (ps.map (mkIdent ∘ Binding.name))
  let ps' := ps ++ [⟨paramName, paramType, BinderInfo.default⟩]
  --if ctx.usePartial then
  --  let letDecls ← mkLocalInstanceLetDecls ctx `Repr header.argNames
  --  body ← mkLet letDecls body
  let binders ← genBindings ps'
  --if ctx.usePartial then
  --  `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent coeTo) := $body:term)
  --else
  let s ← `($(mkIdent coeTo.name))
  let rt ← mkInstantiatedType s (ps.map (mkIdent ∘ Binding.name))
  let ⟨body, cmds⟩ ← mkBody coeFrom coeTo auxFunName (mkIdent paramName)
  let mut r := cmds
  let aux ← `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $rt := $body:term)
  return ⟨aux, r⟩

private def mkMutualBlock
  (coeFrom coeTo:InductiveVal)
: TermElabM (Syntax × Name × Array Command) := do
  let n ← mkFreshUserName `cast
  let ⟨auxDef, cmds⟩  ← mkAuxFunction n coeFrom coeTo
  let stx ← `(mutual
                $auxDef:command
              end)
  return ⟨stx,n, cmds⟩
/-
  up-coercion
  Modeled after the ToExpr instance generator at
    https://github.com/leanprover/lean4/blob/f45c19b428496aa99036d317c2b8bd83dae4e7ea/src/Lean/Elab/Deriving/ToExpr.lean
-/

private def mkCoeInstanceCmd
  (coeFrom coeTo: InductiveVal)
  (t: Expr)
: TermElabM (Array Syntax) := do
  let ⟨ps, _⟩ ← toParams t #[]
  let bs ← genBindings ps
  let f ← mkInstantiatedType (← `($(mkIdent coeTo.name))) (ps.map (mkIdent ∘ Binding.name))
  let t ← mkInstantiatedType (← `($(mkIdent coeFrom.name))) (ps.map (mkIdent ∘ Binding.name))
  let cmds := #[← mkMutualBlock coeFrom coeTo]
  let a := mkIdent (Name.mkStr1 ("SubType_" ++ coeFrom.name.toString ++ "_" ++ coeTo.name.toString))
  let c ← cmds.mapM (λ ⟨_, n, _⟩ ↦ do
      let nTerm ← `($(mkIdent n))
      let n' ← mkInstantiatedType nTerm (ps.map (mkIdent ∘ Binding.name))
      `(instance $a:ident $bs:bracketedBinder* : SubType ($t) ($f) where
          coe := $n'
       )
    )
  let ⟨cmds', temp⟩  := Array.unzip cmds
  let ⟨_ , cmds''⟩   := Array.unzip temp
  return cmds' ++ c ++ cmds''.flatten

def upCoe
  (tSuper tSub: InductiveVal)
: CommandElabM Unit := do
  let cmds ← liftTermElabM <| mkCoeInstanceCmd tSub tSuper tSub.type
  cmds.forM (λ x ↦ do
    logInfo m!"elaborating {x}"
    elabCommand x
    -- logInfo m!"command elaborated"
  )

namespace AR.Lang.Compose.CoeUp
