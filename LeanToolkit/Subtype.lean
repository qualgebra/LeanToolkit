--
-- Subtype.lean
--
import LeanToolkit.Common

open Lean Elab Command Lean.Meta Lean.Elab.Term Lean.Meta.SynthInstance
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std
open Array

private def getSubTypeRel (i: Instance): TermElabM (Option (Name × Name)) := do
  let env ← getEnv
  let n := i.val.constName!
  let v' := env.find? n
  match v' with
  | none => pure none
  | some v =>
      let w := (Expr.getAppArgs ∘ ConstantInfo.type) v
      let p := Prod.mk (w[0]? >>= Expr.constName?) (w[1]? >>= Expr.constName?)
      match p with
      | ⟨ some x, some y ⟩ => pure $ some ⟨ x, y⟩
      | _ => pure none

--
-- find subtypes and their corresponding super-types in the current environment
-- returns an array of ⟨subtypeName, supertypeName⟩ pairs
--
def findSubTypes: TermElabM (Array (Name × Name)) := do
  --let env ← getEnv
  let t ← elabTerm (← `(SubType _ _)) none
  let rs ← getInstances t
  rs.filterMapM getSubTypeRel
  -- pure $
  --   rs.map (Expr.constName! ∘ Instance.val) |>
  --   filterMap (λ v ↦  env.find? v) |>
  --   filterMap (λ v ↦
  --     let w := (Expr.getAppArgs ∘ ConstantInfo.type) v
  --     let p := Prod.mk (w[0]? >>= Expr.constName?) (w[1]? >>= Expr.constName?)
  --     match p with
  --     | ⟨ some x, some y ⟩ => some ⟨ x, y⟩
  --     | _ => none
  --     )

def Lean.Expr.isSubtypeOf: Expr → Expr → TermElabM Bool
| e₁, e₂ => do
    let t₁ ← PrettyPrinter.delab e₁
    let t₂ ← PrettyPrinter.delab e₂
    let t ← elabTerm (← `(SubType $t₁ $t₂)) none
    let rs ← getInstances t
    return !rs.isEmpty

-- def findSuperType (e: Expr): TermElabM (Option SuperType) := do
--   --let env ← getEnv
--   let t ← PrettyPrinter.delab e
--   let trm ← elabTerm (← `(SubType $t _)) none
--   let rs ← getInstances trm
--   if rs.isEmpty then return none
--   else getSubTypeRel rs[0]!

--private
def addFnPair(x y: Name): CommandElabM Unit := do
  let env ← getEnv
  let envContents :=  EnvExtension.getState subfunctionExt env
  let envContents := (x,y) :: envContents
  modifyEnv (subfunctionExt.setState . envContents)

def adjustFnName (env: Environment) (f: Name): Option Expr := do
  let envContents :=  EnvExtension.getState subfunctionExt env
  let o := envContents.find? (λ (x,_) ↦ x.isPrefixOf f)
  match o with
  | some (x,y) => (some ∘ Lean.mkConst) (f.replacePrefix x y)
  | none => none

def adjustSubTypeName (env: Environment) (n: Name): List (Name × Name) → Option Expr
| [] => adjustFnName env n
| ⟨tSub, tSuper⟩ :: xs =>
    if n == tSub then some (mkConst tSuper) else
    if tSub.isPrefixOf n then some (mkConst (n.replacePrefix tSub tSuper)) else
    adjustSubTypeName env n xs

/-
  generalizeSubType

  Given a type name, replace it with its super type name if it has a super type.
-/
def generalizeSubType (env: Environment) (n: Name): List (Name × Name) → Option Expr
| [] => adjustFnName env n
| ⟨tSub, tSuper⟩ :: xs =>
    if tSub.isPrefixOf n then
      ((some ∘ Lean.mkConst) (n.replacePrefix tSub tSuper)) else
    generalizeSubType env n xs
