--
--  FnSum.lean
--
import LeanToolkit.Common
import LeanToolkit.Subtype

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

-- namespace AR.Tools.Compose.FnSum

set_option pp.fieldNotation false

structure Fn where
  name: Name
  type: Expr
  body: Expr
  alts: Array Syntax

def adjustType (env: Environment) (t: Expr) (subs: List (Name × Name)): Expr :=
  t.replace λ e ↦
        match e.constName? with
        | some n' => adjustSubTypeName env n' subs >>= some
        | none => none

def extractAlts (n:Name) (e: Expr) (subs: List (Name × Name)): TermElabM (Array Syntax) := do
  let env ← getEnv
  let s := (e.find? λ e ↦
    let e' := e.eq?
    match e' with
    | some (l, t, r) => t.isAppOf n
    | _ => false)
  --logInfo m!"e: {e} - n: {n}"
  --logInfo m!"s: {s}"

  let e' := if s.isSome then s.get! else e
  let e' := e'.replace λ e ↦
    let c := e.const?
    match c with
    | some (c', _) =>
        let v? := env.find? c'
        match v? with
        | some (ConstantInfo.ctorInfo v) =>
            some (mkConst (v.induct.append v.name) [])
        | _ => none
    | _ => none
  --logInfo m!"e': {e'}"
  let stx:Syntax ← PrettyPrinter.delab e'
  --logInfo m!"expression: {e'}"
  --logInfo m!"expression raw: {e'.dbgToString}"
  --logInfo m!"term: {stx}"
  let m := stx.find? (λ s ↦ s.isOfKind `Lean.Parser.Term.matchAlts)

  match m with
  | some m' =>
      let m' ← m'.replaceM λ stx ↦
        let o := adjustSubTypeName env stx.getId subs
        match o with
        | some (Expr.const x _) => do
            let r ← `($(mkIdent x))
            return (some r)
        | _ => pure none
      let x := m'.getNumArgs
      let y := m'[0].getNumArgs
      --logInfo m!"arg count: {x} {y}"
      return m'[0].getArgs
  | none => return #[]


/-

-/

-- def composeFns (subs: List (Name × Name)): List Fn → TermElabM Fn
-- | [] => throwError "Empty list of functions."
-- | x :: [] => do
--     let env ← getEnv
--     let t := adjustType env x.type subs
--     logInfo m!"alts: {x.alts}"
--     pure (Fn.mk x.name t x.body x.alts)
-- | x :: xs => do
--     let env ← getEnv
--     let r ← composeFns subs xs
--     let t := adjustType env x.type subs
--     logInfo m!"comparing types {t} - {r.type}"
--     if (← isDefEq t r.type) then
--       logInfo m!"composing alts of dims {x.alts.size} and {r.alts.size}"
--       let sum := x.alts ++ r.alts
--       logInfo m!"sum: {sum}"
--       return (Fn.mk x.name t x.body sum)
--     else
--       throwError m!"Failed to sum up different types: {t} - {r.type}"


--end AR.Tools.Compose.FnSum
