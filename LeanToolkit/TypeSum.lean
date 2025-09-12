--
-- TypeSum.lean
--
import LeanToolkit.Common
import LeanToolkit.Subtype
--import AR.Tools.Compose.CoeUp
--import AR.Tools.Compose.CoeDown
import LeanToolkit.Coe

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

-- syntactic category for summing types
declare_syntax_cat types

syntax (name := singleton) ident: types
syntax (name := typeSum) types " |+ " types : types

--
-- create a new hidden inductive type with the explicit constructors
-- then append the name of the created type to the list of types to
-- be summed up
--
private def includeExplicitConstructors
  (d: Ident)
  (sig: TSyntax `Lean.Parser.Command.optDeclSig)
  (cs : TSyntax `types)
  (explicitCs: TSyntaxArray `Lean.Parser.Command.ctor): CommandElabM (TSyntax `types)
:= do
  let hiddenName := Name.append (Name.mkStr1 "hidden") d.getId
  let ⟨_, s⟩  := expandOptDeclSig sig
  -- logInfo m!"sig - {sig} - {s}"
  let hiddenSig:TSyntax `Lean.Parser.Command.optDeclSig ←
    if s.isSome then pure sig else `(optDeclSig| : Type)

  let cmd ← `(inductive $d $hiddenSig where $explicitCs:ctor*)
  -- logInfo m!"hidden command: {cmd}"

  withNamespace (Name.mkStr1 "hidden") (elabCommand cmd)

  `(types| $cs |+ $(mkIdent hiddenName):ident)

--
--  Given a type t, rename any occurrence of any of the sum constituents to the name of the sum type,
--  and any occurrence of a name of a subtype to the name of its corresponding super-type.
--
private def adjustType
  (t: Expr)
  (lhs: Name)
  (types: List InductiveVal)
  (subs: List (Name × Name))
: TermElabM Expr := do
  let env ← getEnv
  return Expr.replace
    (λ e ↦
        match e.constName? with
        | some n' =>
            if (types.map (ConstantVal.name ∘ InductiveVal.toConstantVal)).elem n' then
              some (mkConst lhs)
            else
              match types.find? (λ n ↦ n.toConstantVal.name.isPrefixOf n') with
              | some t => some (Lean.mkConst (n'.replacePrefix t.toConstantVal.name lhs))
              | none => (adjustSubTypeName env n' subs) >>= (some ∘ mkConst)
        | none =>
            none
    ) t

--
--  helper function for turning the constituent type names
--  into a list of names
--
private partial
def getTypeVals': TSyntax `types → TermElabM (List Name)
| `(types| $i:ident) => do
      if (← isInductive i.getId) then
        return [i.getId]
      else
        throwError m!"{i.getId} is not inductive."
| `(types| $l:types |+ $r:types) => do
      let x ← getTypeVals' l
      let y ← getTypeVals' r
       return x ++ y
| _ => return  []

def getTypeVals(cs: TSyntax `types): TermElabM (List InductiveVal) := do
  let ns ← getTypeVals' cs
  let ns' := List.eraseDups ns
  ns'.mapM getInductiveVal

private def countExtraArgs (full part: Expr): TermElabM Nat := do
  let (full', _) ← toParams full #[]
  let (part', _) ← toParams part #[]
  if full'.length >= part'.length then
    return full'.length - part'.length
  else
    throwError m!"types {full} and {part} are incompatible."

private def getTypeDeltas
  (expectedType: Expr)
  (types: List InductiveVal)
  (lhs: Name)
  (subs: List (Name × Name))
: TermElabM (List Nat) := do
  let ts ← types.mapM (λ x ↦ adjustType x.type lhs types subs)
  let r  ← ts.mapM (λ x ↦ countExtraArgs expectedType x)
  return r

private def checkTypeCompat
  (types: List InductiveVal)
  (lhs: Name)
  (subs: List (Name × Name))
: TermElabM Expr := do
  match types with
  | [] => throwError m!"empty list of types"
  | t :: ts =>
      let t ← adjustType t.type lhs types subs
      if ts.isEmpty then return t
      else
        let e ← checkTypeCompat ts lhs subs
        let c ←
          if ←((isDefEq t e))
          then return e
          else throwError m!"{t} and {e} are different types."

def concatConstructors
  (css: List (List TracedConstructor))
: TermElabM (List TracedConstructor) := do
  match css with
  | [] => return []
  | cs :: css' =>
      let mut result: List TracedConstructor := cs
      let c₂ ← concatConstructors css'
      for c in c₂ do
        if let some c' := result.find? (λ c'' ↦ c.name == c''.name) then
          if c.type != c'.type then
            throwError "constructors of same name and mismatching types"
        else result := result.append [c]
      return result

private def getCtors (typ : InductiveVal × Nat): TermElabM (List TracedConstructor) := do
  let env ← getEnv
  let ci := List.map (λ c ↦ (env.find? c)) typ.1.ctors
  let cs ← List.mapM constantInfo2Constructor ci
  return List.map (λ c ↦ ⟨c.name, some c.type, typ.1, typ.2⟩) cs

--
--  implementation of the type sum elaborator
--
private def typeSumImp
  (ts: List InductiveVal)
  (expectedType?: Option Expr)
  (lhs:Name)
  (subs: List (Name × Name)):
TermElabM (List (List TracedConstructor) × Expr × List Binding) := do
  let mut e: Expr := .const (Name.anonymous) []
  let mut deltas: List Nat := ts.map (λ _ ↦ 0)

  match expectedType? with
    | some t =>
        deltas ← getTypeDeltas t ts lhs subs
        e := t
    | none =>
      e ← checkTypeCompat ts lhs subs

  --if deltas.isEmpty then throwError "Incompatible types"

  let (bvars, _) ← toParams e #[]
  --let ts := ts.map getTypeName
  --let ts := ts.eraseDups
  --let ts ← ts.mapM getInductiveVal
  let css ← (List.zip ts deltas).mapM getCtors

  return ⟨css, e, bvars⟩

def adjustConstructorType (name: Name) (e: Expr) (extraArgs: Nat): Expr :=
  if extraArgs = 0 then e else
    let dontCare := .const (Name.mkStr1 "_") []
    e.replace λ x ↦
      match x with
      | .app (.const n us) e' =>
          if (n == name) then
            some <| .app (.app (.const n us) dontCare)
                         (adjustConstructorType name e' (extraArgs -1))
          else
            none
      | _ => none

--
--  elaborator for type sum syntax
--
elab "inductive " d:ident sig':optDeclSig " := " cs':types explicitCs: ctor* : command => do
  let mut cs := cs'
  let lhs := d.getId

  -- explicit constructors
  --if explicitCs.size > 0 then
  --  cs ← includeExplicitConstructors d sig' cs explicitCs

  -- subtypes
  let subs ← liftTermElabM <| findSubTypes
  let (_, optSig) := expandOptDeclSig sig'
  let expectedType ← optSig.bindM (λ s ↦ do pure <| some (← liftTermElabM <| elabType s))

  logInfo m!"expected type: {expectedType}"
  let ts ← liftTermElabM <| getTypeVals cs
  let ⟨css, e, _⟩ ← liftTermElabM <| typeSumImp ts expectedType lhs subs.toList
  let cs' ← liftTermElabM <| concatConstructors css
  let cObjs ← List.mapM (
            λ n ↦ do
              let r := n.type
              --logInfo m!"discarding return: {n.type} - {r}"
              let t' ←
                (match r with
                | some r' => do
                              let x ← liftTermElabM <| adjustType r' lhs ts subs.toList
                              return (some x)
                | none => return none)
              --logInfo m!"adjusted {n.type} to {t'}"
              let t' := match t' with
                        | some t => adjustConstructorType lhs t n.extraParams
                        | none => t'
              return TracedConstructor.mk n.name t' n.source n.extraParams) cs'

  let cStx ← cObjs.mapM (λ c ↦ do
        match c.type with
        | some t' =>
            let t ← liftTermElabM <| PrettyPrinter.delab t'
            `(ctor| |$(mkIdent c.name):ident : $t:term)
        | none => `(ctor| |$(mkIdent c.name):ident))

  let cStx := cStx.toArray ++ explicitCs
  let e' ← liftTermElabM <| PrettyPrinter.delab e
  let cmd ← `(inductive $(mkIdent lhs) : $e' $cStx:ctor*)
  logInfo m!"elaborating {cmd}"
  elabCommand cmd

  let s ← liftTermElabM <| getInductiveVal lhs
  let propType ← liftTermElabM <| isPropFormerType s.type

  if !propType then
    genCoeInst lhs e cObjs
    for t in ts do
      let t ← liftTermElabM <| getInductiveVal t.name
      --upCoe s t
      --downCoe t s
