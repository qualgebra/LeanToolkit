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

namespace AR.Tools.Compose.FnSum

set_option pp.fieldNotation false

-- syntactic category for summing functions
declare_syntax_cat functions

abbrev altT := Lean.Parser.Term.matchAlt

syntax (name := singleton) ident: functions
syntax (name := funSum) functions " |+ " functions : functions
--syntax (name := expAlts) functions : functions

structure Fn where
  name: Name
  type: Expr
  body: Expr
  alts: Array Syntax

private partial
def getFnVals': TSyntax `functions → TermElabM (List Name)
| `(functions| $i:ident) => return [i.getId]
| `(functions| $l:functions |+ $r:functions) => do
      let x ← getFnVals' l
      let y ← getFnVals' r
       return x ++ y
| _ => return  []

def adjustType (env: Environment) (t: Expr) (subs: List (Name × Name)): Expr :=
  t.replace λ e ↦
        match e.constName? with
        | some n' => adjustSubTypeName env n' subs >>= (some ∘ mkConst)
        | none => none

#print ConstructorVal
#print Constructor
def extractAlts (n:Name) (e: Expr) (subs: List (Name × Name)): TermElabM (Array Syntax) := do
  let env ← getEnv
  let s := (e.find? λ e ↦
    let e' := e.eq?
    match e' with
    | some (l, t, r) => t.isAppOf n
    | _ => false)
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
  let stx:Syntax ← PrettyPrinter.delab e'
  logInfo m!"expression: {e'}"
  logInfo m!"expression raw: {e'.dbgToString}"
  logInfo m!"term: {stx}"
  let m := stx.find? (λ s ↦ s.isOfKind `Lean.Parser.Term.matchAlts)

  match m with
  | some m' =>
      let m' ← m'.replaceM λ stx ↦
        let o := adjustSubTypeName env stx.getId subs
        match o with
        | some x => do
            let r ← `($(mkIdent x))
            return (some r)
        | none => pure none
      let x := m'.getNumArgs
      let y := m'[0].getNumArgs
      logInfo m!"arg count: {x} {y}"
      return m'[0].getArgs
  | none => return #[]

def getFnVals (lhs: Name) (stx: TSyntax `functions) (subs: List (Name × Name)): CommandElabM (List Fn) := do
  let fs' ← liftTermElabM <| getFnVals' stx
  let fs := List.eraseDups fs'
  logInfo m!"functions: {fs}"
  --let env ← getEnv

  fs.forM λ f ↦
    addFnPair f lhs

  fs.mapM λ f' ↦ do
    let o ← liftTermElabM <| Lean.Meta.getUnfoldEqnFor? f'

    --logInfo m!"looking for {o}"
    let alts ←
      match o with
      | some n => do
          liftTermElabM <| extractAlts f' ((← getConstInfo n).value!) subs
      | _ => pure #[]

    let t := (← getConstInfo f').type

    return (Fn.mk f' t ((← getConstInfo f').value!) alts)

def composeFns (subs: List (Name × Name)): List Fn → TermElabM Fn
| [] => throwError "Empty list of functions."
| x :: [] => do
    let env ← getEnv
    let t := adjustType env x.type subs
    pure (Fn.mk x.name t x.body x.alts)
| x :: xs => do
    let env ← getEnv
    let r ← composeFns subs xs
    let t := adjustType env x.type subs
    logInfo m!"comparing types {t} - {r.type}"
    if (← isDefEq t r.type) then
      logInfo m!"composing alts of dims {x.alts.size} and {r.alts.size}"
      return (Fn.mk x.name t x.body (x.alts ++ r.alts))
    else
      throwError m!"Failed to sum up different types: {t} - {r.type}"
#check matchAlts
--
--  elaborator for type sum syntax
--
elab "fn " d:ident sig':optDeclSig " := " fs':functions as:altT* : command => do
  let lhs := d.getId

  -- subtypes
  let subs ← liftTermElabM <| findSubTypes
  logInfo m!"subs: {subs}"
  let (_, optSig) := expandOptDeclSig sig'
  let expectedType ← optSig.bindM (λ s ↦ do pure <| some (← liftTermElabM <| elabType s))

  let fs ← getFnVals lhs fs' subs.toList

  logInfo m!"{fs.map Fn.name} - {fs.map Fn.type} - {fs.map Fn.body}"

  let fn ← liftTermElabM <| composeFns subs.toList fs

  logInfo m!"number of alts: {fn.alts.size}"

  let (ps, r) ← liftTermElabM <| toParams fn.type #[]
  let r' ← liftTermElabM <| PrettyPrinter.delab r

  let mut p := `x

  let sig ← liftTermElabM <| PrettyPrinter.delab fn.type
    --match ps with
    --| []      => throwError "empty parameter list"
    --| x :: _  =>
        --p := x.name
    --    liftTermElabM <| genBindings ps

  let body ←
    if fn.alts.isEmpty then
      liftTermElabM <| PrettyPrinter.delab fn.body
    else
      let xs := TSyntaxArray.mk (fn.alts ++ as.raw)
      let v ← liftTermElabM <| mkFreshIdent sig
      `(fun $v => match $v:ident with $xs:matchAlt*)

  let cmd ← `(def $d : $sig := $body)

  logInfo m!"elaborating {cmd}"
  elabCommand cmd

end AR.Tools.Compose.FnSum
