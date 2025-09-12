--
--  CoeDown.lean
--
import LeanToolkit.Common

open Lean Elab Command Lean.Meta Lean.Elab.Term Lean.Meta.SynthInstance Lean.Elab.Deriving
open AR.Tools.Compose.Common
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

namespace AR.Tools.Compose.CoeDown

-- TODO: refactor the two copies, here and in CoeUp
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

def downCoeCmds
  (tSuper tSub: InductiveVal)
: TermElabM (Array Command) := do
  let mut cmds := #[]
  let ty := tSuper.type
  let ⟨params, _⟩ ← toParams ty #[]
  let argNames ← mkInductArgNames tSuper
  for ctorName in tSuper.ctors do
    let ctorInfo ← getConstInfoCtor ctorName

    let ⟨patterns, rhs', bindings, _⟩ ←
      forallTelescopeReducing ctorInfo.type λ xs _ => do
        mkRhs tSuper tSub ctorName argNames `coe xs

      let bs ← genBindings (params ++ bindings)
      let f' ← `($(mkIdent tSub.name))
      let f ← mkInstantiatedType f' (params.map (mkIdent ∘ Binding.name))
      let t' ← `($(mkIdent tSuper.name))
      let t ← mkInstantiatedType t' (params.map (mkIdent ∘ Binding.name))
      let some coe := patterns[0]? | throwError m!"patterns is empty in downCoeCmds"
      let downCast ← `(instance $bs:bracketedBinder* : CoeDep $f $rhs' $t where
                        coe := $coe
                      )
      cmds := cmds.push downCast
  return cmds

def downCoe
  (tSuper tSub: InductiveVal)
: CommandElabM Unit := do
  let cmds ← liftTermElabM <| downCoeCmds tSuper tSub
  for c in cmds do
    logInfo m!"elaborating {c}"
    elabCommand c

end AR.Tools.Compose.CoeDown
