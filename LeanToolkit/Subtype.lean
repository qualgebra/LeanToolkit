--
-- Subtype.lean
--
import LeanToolkit.Common

open Lean Elab Command Lean.Meta Lean.Elab.Term Lean.Meta.SynthInstance
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

--
-- find subtypes and their corresponding super-types in the current environment
--
def findSubTypes: TermElabM (Array (Name × Name)) := do
  let env ← getEnv
  --let st := env.find? `SubType
  --let rs ← match st with
  --          | some _ =>
  --                try
                    let stx ← `(SubType _ _)
                    let t ← elabTerm stx none --false
                    let rs ← getInstances t
  --                catch _ => do
  --                  return #[]
  --          | none => return #[]

  let relevantVals := Array.map (Expr.constName! ∘ Instance.val) rs
  let relevantVals' := relevantVals.filterMap (λ v ↦  env.find? v)
  let ts := relevantVals'.filterMap (λ v ↦
    let w := (Expr.getAppArgs ∘ ConstantInfo.type) v
    let p := Prod.mk (w[0]? >>= Expr.constName?) (w[1]? >>= Expr.constName?)
    match p with
    | ⟨ some x, some y ⟩ => some ⟨ x, y⟩
    | _ => none
    )
  return ts

def adjustFnName (env: Environment) (f: Name): Option Name := do
  let envContents :=  EnvExtension.getState envExt env
  let o := envContents.find? (λ (x,_) ↦ x.isPrefixOf f)
  match o with
  | some (x,y) => some (f.replacePrefix x y)
  | none => none

def addFnPair(x y: Name): CommandElabM Unit := do
  let env ← getEnv
  let envContents :=  EnvExtension.getState envExt env
  let envContents := (x,y) :: envContents
  modifyEnv (envExt.setState . envContents)

def adjustSubTypeName (env: Environment)  (n: Name): List (Name × Name) → Option Name
| [] => adjustFnName env n
| ⟨tSub, tSuper⟩ :: xs =>
    if tSub.isPrefixOf n then
      (some (n.replacePrefix tSub tSuper)) else
    adjustSubTypeName env n xs
