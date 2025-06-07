/-
  Type Algebra meta-programming
-/
import Lean
import Lean.Elab.Term

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term
open Lean.Elab.Deriving
open Lean.Meta.SynthInstance
open Meta
open Std

namespace TAlgebra

class SubType (tSub tSuper: Type) extends Coe tSub tSuper

--
--  a TracedConstructor binds a constructor object to the
--  original type where it comes from
--
structure TracedConstructor where
  ctor:   Constructor
  source: InductiveVal

structure Binding where
  name: Ident
  type: TSyntax `term
deriving Repr

def constantInfo2Constructor (ci': Option ConstantInfo): CommandElabM Constructor :=
  match ci' with
  | some ci =>
      let cs := ci.name.components
      let n := dite (cs ≠ []) (λ ne ↦ List.getLast cs ne) (λ _ ↦ Name.anonymous)
      return (Constructor.mk n ci.type)
  | _ => throwError "not a ConstantInfo object"

open Parser.Command

-- syntactic category for summing types
declare_syntax_cat ctors

syntax (name := singleton) ident: ctors
syntax (name := typeSum) ctors " + " ctors : ctors

def getInductiveVal(typ: Name): CommandElabM InductiveVal := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) => return val
  | _ => throwError m!"{typ} is not and inductive value"

def getCtors (typ : InductiveVal) : CommandElabM (List TracedConstructor) := do
  let env ← getEnv
  let ci := List.map (λ c ↦ (env.find? c)) typ.ctors
  let cs ← List.mapM constantInfo2Constructor ci
  return List.map (λ c ↦ ⟨c, typ⟩) cs

def adjustSubTypeName (n: Name): List (Name × Name) → Option Expr
| [] => none
| ⟨tSub, tSuper⟩ :: xs =>
    if n == tSub then some (mkConst tSuper) else
    if tSub.isPrefixOf n then some (mkConst (n.replacePrefix tSub tSuper)) else
    adjustSubTypeName n xs

--
--  Given a type t, rename any occurrence of any of the sum constituents to the name of the sum type,
--  and any occurrence of a name of a subtype to the name of its corresponding super-type.
--
def adjustType (t: Expr) (lhs: Name) (types: List InductiveVal) (subs: List (Name × Name)): TermElabM Expr := do
  return Expr.replace
    (λ e ↦
        match e.constName? with
        | some n' =>
            if (types.map (ConstantVal.name ∘ InductiveVal.toConstantVal)).elem n' then
              some (mkConst lhs)
            else
              match types.find? (λ n ↦ n.toConstantVal.name.isPrefixOf n') with
              | some t => some (Lean.mkConst (n'.replacePrefix t.toConstantVal.name lhs))
              | none => adjustSubTypeName n' subs
        | none =>
            none
    ) t

def checkTypeCompat(types: List InductiveVal) (lhs: Name) (subs: List (Name × Name)): TermElabM Expr := do
  match types with
  | [] => throwError m!"empty list of types"
  | t :: ts =>
      let t₁' ← adjustType t.type lhs types subs
      if ts.isEmpty then return t₁'
      else
        let e ← checkTypeCompat ts lhs subs
        let c ←
        if ←((isDefEq t₁' e))
        then return e
        else throwError m!"{t₁'} and {e} are different types."

def concatConstructors (css: List (List TracedConstructor)): CommandElabM (List TracedConstructor) := do
  match css with
  | [] => return []
  | cs :: css' =>
      let mut result: List TracedConstructor := cs
      let c₂ ← concatConstructors css'
      for c in c₂ do
        if let some c' := result.find? (λ c'' ↦ c.ctor.name == c''.ctor.name) then
          if c.ctor.type != c'.ctor.type then
            throwError "constructors of same name and mismatching types"
        else result := result.append [c]
      return result

--
--  implementation of the type sum elaborator
--
def typeSumImp (ts: List InductiveVal) (lhs:Name) (subs: List (Name × Name)): CommandElabM (List (List TracedConstructor) × Expr) := do
  let e ← liftTermElabM <| checkTypeCompat ts lhs subs
  let css ← ts.mapM getCtors
  return ⟨css, e⟩

--
--  helper function for turning the constituent type names
--  into a list of names
--
private partial
def getTypeVals': TSyntax `ctors → CommandElabM (List Name)
| `(ctors| $i:ident) => do
      if (← isInductive i.getId) then
        return [i.getId]
      else
        throwError m!"{i.getId} is not inductive."
| `(ctors| $l:ctors + $r:ctors) => do
      let x ← getTypeVals' l
      let y ← getTypeVals' r
      return x ++ y
| _ => return  []

--
--  taking a syntactic sum expression and returning a list of type names
--  with no duplicates
--
def getTypeVals(cs: TSyntax `ctors): CommandElabM (List InductiveVal) := do
  let ns ← getTypeVals' cs
  let ns' := List.eraseDups ns
  ns'.mapM getInductiveVal

def toParams: Expr → TermElabM (List Binding)
| .forallE _ t b bi => do
    let b' ← toParams b
    let id := mkIdent (← mkFreshUserName `x)
    let t' ← PrettyPrinter.delab t
    let r :=
      if bi.isImplicit then
        b'
      else
        ⟨id, t'⟩ :: b'
    return r
| _ => return []

def genBinder (b: Binding): TermElabM (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let t := b.type
  `(bracketedBinder| ($(b.name) : $t))

def genBindings: List Binding → TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder)
| []       => return #[]
| b :: bs' => do
    let h ← genBinder b
    let t ← genBindings bs'
    let all:TSyntaxArray `Lean.Parser.Term.bracketedBinder := TSyntaxArray.mk (h :: t.toList).toArray
    return all

def mkInstantiatedType (t: TSyntax `term): List Ident → TermElabM (TSyntax `term)
| [] => return t
| n :: ns' => do
    let r ← `($t $n)
    mkInstantiatedType r ns'

/-
  Modified version of the one at
    https://github.com/leanprover/lean4/blob/f45c19b428496aa99036d317c2b8bd83dae4e7ea/src/Lean/Elab/Deriving/Repr.lean
-/
def mkRhs
  (coeFrom coeTo: InductiveVal)
  (ctorName: Name)
  (argNames: Array Name)          -- arguments of the coeFrom type
  (fnName: Name)                  -- name of the coercion function
  (cnsType: Expr)
  (xs: Array Expr)
: TermElabM (Array (TSyntax `term) × TSyntax `term × Expr × List Binding × TSyntax `term) := do
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
    let a ← mkIdent <$> if i < coeFrom.numParams then pure argNames[i]! else mkFreshUserName `a
    if i < coeFrom.numParams then
      ctorArgs := ctorArgs
      -- add `_` for inductive parameters, they are inaccessible
      --ctorArgs := ctorArgs.push (← `(_))
    else
      ctorArgs := ctorArgs.push a

    if (← x.fvarId!.getBinderInfo).isExplicit then
      let paramType ← inferType x
      bindings := bindings.push ⟨a, ← PrettyPrinter.delab paramType⟩
      logInfo m!"paramType: {paramType} -- coeFrom: {coeFrom.name}"
      if paramType.constName == coeFrom.name || paramType.isAppOf coeFrom.name then
        rhs ← `($rhs ($(mkIdent fnName) $a:ident))
        logInfo m!"paramType match!!!  {rhs}"
      else if (← isType x <||> isProof x) then
        rhs ← `($rhs "_")
      else
        rhs ← `($rhs $a)
  patterns := patterns.push (← `($(mkIdent ctorName):ident $ctorArgs:term*))
  rhs' ← `($rhs' $ctorArgs:term*)
  return ⟨patterns, rhs', cnsType, bindings.toList, rhs⟩

def mkBody
  (coeFrom coeTo: InductiveVal)
  (auxFunName: Name)
  (paramName: Ident)
  (summedTypes: List InductiveVal)
  (subs : List (Name × Name))
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
      let cnsType := ctorInfo.type

      let ⟨patterns, rhs', cnsType, bindings, rhs⟩ ← forallTelescopeReducing ctorInfo.type λ xs _ => do
        mkRhs coeFrom coeTo ctorName argNames auxFunName cnsType xs

      let alt ← `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt

      --let downCast ← `(instance $bs:bracketedBinder* : CoeDep $f $rhs' $t where
      --                  coe := $(patterns[0]!)
      --                )
      --cmds := cmds.push downCast
    return ⟨alts, cmds⟩

def mkAuxFunction
  (auxFunName : Name)
  (coeFrom coeTo: InductiveVal)
  (summedTypes: List InductiveVal)
  (subs : List (Name × Name))
: TermElabM (Command × Array Command) := do
  let ps ← (toParams coeFrom.type)
  let paramName := mkIdent (← mkFreshUserName `x)
  let paramType' ← `($(mkIdent coeFrom.name))
  let paramType ← mkInstantiatedType paramType' (ps.map Binding.name)
  let ps' := ps ++ [⟨paramName, paramType⟩]
  --if ctx.usePartial then
  --  let letDecls ← mkLocalInstanceLetDecls ctx `Repr header.argNames
  --  body ← mkLet letDecls body
  let binders ← genBindings ps'
  --if ctx.usePartial then
  --  `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent coeTo) := $body:term)
  --else
  let s ← `($(mkIdent coeTo.name))
  let rt ← mkInstantiatedType s (ps.map Binding.name)
  let ⟨body, cmds⟩ ← mkBody coeFrom coeTo auxFunName paramName summedTypes subs
  let mut r := cmds
  let aux ← `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $rt := $body:term)
  return ⟨aux, r⟩

def mkMutualBlock
  (coeFrom coeTo:InductiveVal)
  (summedTypes: List InductiveVal)
  (subs : List (Name × Name))
: TermElabM (Syntax × Name × Array Command) := do
  let n ← mkFreshUserName `cast --(Name.appendAfter coeFrom.name "_to_") ++ coeTo.name
  let ⟨auxDef, cmds⟩  ← mkAuxFunction n coeFrom coeTo summedTypes subs
  let stx ← `(mutual
                $auxDef:command
              end)
  return ⟨stx,n, cmds⟩

/-
  Down-coercion
  Modeled after the ToExpr instance generator at
    https://github.com/leanprover/lean4/blob/f45c19b428496aa99036d317c2b8bd83dae4e7ea/src/Lean/Elab/Deriving/ToExpr.lean
-/

private def mkCoeInstanceCmd
  (coeFrom coeTo: InductiveVal)
  (t: Expr)
  (summedTypes: List InductiveVal)
  (subs : List (Name × Name))
: TermElabM (Array Syntax) := do
  let ps ← toParams t
  let bs ← genBindings ps
  let f ← mkInstantiatedType (← `($(mkIdent coeTo.name))) (ps.map Binding.name)
  let t ← mkInstantiatedType (← `($(mkIdent coeFrom.name))) (ps.map Binding.name)
  let cmds := #[← mkMutualBlock coeFrom coeTo summedTypes subs]
  let a := mkIdent (Name.mkStr1 ("SubType_" ++ coeFrom.name.toString ++ "_" ++ coeTo.name.toString))
  let c ← cmds.mapM (λ ⟨_, n, _⟩ ↦ do
      let nTerm ← `($(mkIdent n))
      let n' ← mkInstantiatedType nTerm (ps.map Binding.name)
      `(instance $a:ident $bs:bracketedBinder* : SubType ($t) ($f) where
          coe := $n'
       )
    )
  let ⟨cmds', temp⟩  := Array.unzip cmds
  let ⟨_ , cmds''⟩   := Array.unzip temp
  return cmds' ++ c ++ cmds''.flatten

def upCoe
  (tSuper tSub: InductiveVal)
  (t: Expr)
  (summedTypes: List InductiveVal)
  (subs : List (Name × Name))
: CommandElabM Unit := do
  let cmds ← liftTermElabM <| mkCoeInstanceCmd tSub tSuper t summedTypes subs
  cmds.forM (λ x ↦ do
    logInfo m!"cmd: {x}"
    elabCommand x
    logInfo m!"command elaborated"
  )

def downCoeCmds
  (tSuper tSub: InductiveVal)
: TermElabM (Array Command) := do
  let mut cmds := #[]
  let ty := tSuper.type
  let params ← toParams ty
  let argNames ← mkInductArgNames tSuper
  for ctorName in tSuper.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let cnsType := ctorInfo.type

    let ⟨patterns, rhs', cnsType, bindings, rhs⟩ ←
      forallTelescopeReducing ctorInfo.type λ xs _ => do
        mkRhs tSuper tSub ctorName argNames `coe cnsType xs

      let bs ← genBindings (params ++ bindings)
      let f' ← `($(mkIdent tSub.name))
      let f ← mkInstantiatedType f' (params.map Binding.name)
      let t' ← `($(mkIdent tSuper.name))
      let t ← mkInstantiatedType t' (params.map Binding.name)

      let downCast ← `(instance $bs:bracketedBinder* : CoeDep $f $rhs' $t where
                        coe := $(patterns[0]!)
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

--
-- find subtypes and their corresponding super-types in the current environment
--
def findSubTypes: TermElabM (Array (Name × Name)) := do
  let env ← getEnv
  let stx ← `(SubType _ _)
  let t ← elabTerm stx none
  let rs ← getInstances t
  let relevantVals := Array.map (Expr.constName! ∘ Instance.val) rs
  let relevantVals' := relevantVals.filterMap (λ v ↦  env.find? v)
  logInfo m!"relevantVals: {relevantVals'.map (Expr.getAppArgs ∘ ConstantInfo.type)}"
  let ts := relevantVals'.filterMap (λ v ↦
    let w := (Expr.getAppArgs ∘ ConstantInfo.type) v
    let p := Prod.mk (w[0]? >>= Expr.constName?) (w[1]? >>= Expr.constName?)
    match p with
    | ⟨ some x, some y ⟩ => some ⟨ x, y⟩
    | _ => none
    )
  return ts


--
-- create a new hidden inductive type with the explicit constructors
-- then append the name of the created type to the list of types to
-- be summed up
--
def includeExplicitConstructors
  (d: Ident)
  (sig: TSyntax `Lean.Parser.Command.optDeclSig)
  (cs : TSyntax `ctors)
  (explicitCs: TSyntaxArray `Lean.Parser.Command.ctor): CommandElabM (TSyntax `ctors)
:= do
  let hiddenName := Name.append (Name.mkStr1 "hidden") d.getId
  let ⟨_, s⟩  := expandOptDeclSig sig
  logInfo m!"sig - {sig} - {s}"
  let hiddenSig:TSyntax `Lean.Parser.Command.optDeclSig ←
    if s.isSome then pure sig else `(optDeclSig| : Type)

  let cmd ← `(inductive $d $hiddenSig where $explicitCs:ctor*)
  logInfo m!"hidden command: {cmd}"

  withNamespace (Name.mkStr1 "hidden") (elabCommand cmd)

  `(ctors| $cs + $(mkIdent hiddenName):ident)

elab "inductive " d:ident sig:optDeclSig " := " cs':ctors explicitCs: ctor* : command => do
  let mut cs := cs'

  -- explicit constructors
  if explicitCs.size > 0 then
    cs ← includeExplicitConstructors d sig cs explicitCs

  -- subtypes
  let subs ← liftTermElabM <| findSubTypes

  -- generate and elaborate sum type
  let lhs := d.getId
  let ts ← getTypeVals cs
  let ⟨css, e⟩ ← typeSumImp ts lhs subs.toList
  let cs' ← concatConstructors css
  let r ← List.mapM (
            λ n ↦ do
              let t' ← liftTermElabM <| adjustType n.ctor.type lhs ts subs.toList
              return ⟨Constructor.mk (lhs.append n.ctor.name) t', n.source⟩
            )
          cs'

  let i := InductiveType.mk d.getId e (List.map TracedConstructor.ctor r)
  let decl := Declaration.inductDecl [] 0 [i] false
  liftTermElabM <| addDecl decl

  --
  --  if the sum type is not a Prop, generate Coe and CoeDep instances
  --
  let propType ← liftTermElabM <| isPropFormerType e

  if !propType then
    let s ← getInductiveVal lhs
    for t in ts do
      upCoe s t e ts subs.toList
      downCoe t s

end TAlgebra

open TAlgebra

/-
  Testing
-/

inductive T1
| C1
| C2

inductive T2 where
| C3

inductive T3 where
| C1 (n: Nat)
| C2

inductive T4 (x: Nat) where
| C4
| C5

inductive T5 (y: Nat) where
| C4 (n: Nat)
| C5

inductive T6 (z: Nat) (w: Fin z) where
| C4

inductive T7 (x: Nat) (y: Fin x) where
| C5 (n: Fin x)

inductive sum1 := T1 + T2 + T2 + T1
| EC

#print sum1
def x: T1 := T1.C1

def y: sum1 := x      -- invalid assignment without an up-cast
def z: T1 := sum1.C1  -- invalid assignment without a down-cast

inductive sum2 := T2 + T3
#print sum2

#print T4
inductive sum3 := T4 + T4
#print sum3


#print T5
inductive sum4 := T5 + T5
#print sum4

/-
#print T6
inductive sum5:= T6 + T7 + T6
#print sum5
-/
