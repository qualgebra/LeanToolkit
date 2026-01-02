--
-- TypeSum.lean
--
import LeanToolkit.Common
--import LeanToolkit.Syntax
import LeanToolkit.Subtype
--import LeanToolkit.CoeUp
--import LeanToolkit.CoeDown
--import LeanToolkit.Coe

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

--
--  Given a type t, rename any occurrence of any of the sum constituents to the name of the sum type,
--  and any occurrence of a name of a subtype to the name of its corresponding super-type.
--
private def adjustType
  (t: Expr)
  (lhs: Name)
  (types: List InductiveVal)
  (subs: Array (Name × Name))
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
              | none => (generalizeSubType env n' subs.toList) >>= (some ∘ mkConst)
        | none =>
            none
    ) t

/-
private def countExtraArgs (full part: Expr): TermElabM Nat := do
  let (full', _) ← toParams full #[]
  let (part', _) ← toParams part #[]
  if full'.length ≥ part'.length then
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
-/

private def checkTypeCompat
  (types: List InductiveVal)
  (lhs: Name)
  (subs: Array (Name × Name))
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
--  implementation of the type sum elaborator
--
def typeSumImp
  (ts: List InductiveVal)
  (expectedType?: Option Expr)
  (lhs:Name):
TermElabM (List TracedConstructor × Expr × List Binding) := do
  let mut e: Expr := .const (Name.anonymous) []
  let mut deltas: List Nat := ts.map (λ _ ↦ 0)

  -- subtypes
  let subs ← findSubTypes

  match expectedType? with
    | some t =>
        --deltas ← getTypeDeltas t ts lhs subs
        e := t
    | none =>
      e ← checkTypeCompat ts lhs subs

  --if deltas.isEmpty then throwError "Incompatible types"

  let (bvars, _) ← toParams e #[]
  let css ← (List.zip ts deltas).mapM getCtors

  let cs' ← concatConstructors css
  let cObjs ← List.mapM (
    λ n ↦ do
      let r := n.type
      --logInfo m!"discarding return: {n.type} - {r}"
      let t' ←
        (match r with
        | some r' => do
                      let x ← adjustType r' lhs ts subs
                      return (some x)
        | none => return none)
      --logInfo m!"adjusted {n.type} to {t'}"
      let t' := match t' with
                | some t => adjustConstructorType lhs t n.extraParams
                | none => t'
      return TracedConstructor.mk n.name t' n.source n.extraParams) cs'

  return ⟨cObjs, e, bvars⟩
