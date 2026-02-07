/-
  Syntax.lean

  Exntended syntax for type and function sums.
-/
import LeanToolkit.Common
import LeanToolkit.TypeSum
import LeanToolkit.FnSum
import LeanToolkit.Coe

open Lean Lean.Meta
open Elab
open Command
open Lean.Elab.Term
--open Lean.Parser.Term
open Lean.Parser.Command
--open Meta
--open Std

/-

  Function summation syntax

-/

-- syntactic category for summing functions
declare_syntax_cat functions

abbrev altT := Lean.Parser.Term.matchAlt

syntax (name := singletonFn) ident: functions
syntax (name := funSum) functions " |+ " functions : functions
--syntax (name := expAlts) functions : functions

private partial
def getFnVals': TSyntax `functions → TermElabM (List Name)
| `(functions| $i:ident) => return [i.getId]
| `(functions| $l:functions |+ $r:functions) => do
      let x ← getFnVals' l
      let y ← getFnVals' r
       return x ++ y
| _ => return  []

def getFnVals (lhs: Name) (stx: TSyntax `functions) (subs: List (Name × Name)): CommandElabM (List Fn × Expr) := do
  let fs' ← liftTermElabM <| getFnVals' stx
  let fs := List.eraseDups fs'
  --logInfo m!"functions: {fs}"
  let env ← getEnv

  fs.forM λ f ↦
    addFnPair f lhs

  let mut fnType: Option Expr := none
  let mut ret: List Fn := []

  for f' in fs do
    let o' ← liftTermElabM <| Lean.Meta.getUnfoldEqnFor? f'
    let o := match o' with
             | some x => x
             | _ => f'

    let alts ← liftTermElabM <| extractAlts f' ((← getConstInfo o).value!) subs

    --logInfo m!"found alts: {alts}"
    let t := /-adjustType-/ (← getConstInfo f').type --subs

    if h: fnType.isSome then
      let t₁ := adjustType env t subs
      let t₂ := adjustType env (fnType.get h) subs
      let e ← liftTermElabM <| Meta.isDefEq t₁ t₂
      if !e then throwError "Incompatible function types {t₁} and {t₂}."
    else
      fnType := some t

    ret := (Fn.mk f' t ((← getConstInfo f').value!) alts) :: ret

  return (ret.reverse, fnType.get!)

open Parser.Term

def findSubFunction(fns: List Fn) (source: InductiveVal): MetaM (Option Fn) := do
  if h: fns.length = 1 then pure (fns[0]) else
  fns.findM? λ f ↦ do
    if h: f.type.isForall then
      let firstArg := f.type.forallDomain h
      let n := Lean.mkConst source.name []
      --logInfo m!"matching {firstArg} with {n}"
      Meta.isDefEq n firstArg
    else pure false

def paramCount: Expr → Nat
| .forallE _ _ e _ => 1 + paramCount e
| _ => 0

def abstractConstructor(c: TracedConstructor): MetaM (TSyntax `term) := do
  let n := if c.type.isSome then paramCount c.type.get! else 0
  let mut ps: List (TSyntax `term) := []
  for _ in List.range n do
    ps := mkIdent (← mkFreshBinderName) :: ps
  `(.$(mkIdent c.name) $(ps.toArray):term*)

def generateMatchAlts(s: SuperType) (fns: List Fn) (ps: TSyntaxArray `ident): MetaM (TSyntaxArray `Lean.Parser.Term.matchAlt) := do
  let cs := s.cs.filter (not ∘ isRecursiveConstructor)
  let alts ← cs.mapM λ c ↦ do
    --logInfo m!"constructor: {c.name} - {s.type}"
    --let cnsTerm := mkIdent c.name
    let some f ← findSubFunction fns c.source | throwError "Function with matching source not found."
    let lhs: TSyntax `term ← abstractConstructor c
    let rhs: TSyntax `term ← `($(mkIdent f.name) $ps* ($lhs))
    `(matchAltExpr| | $lhs => $rhs)

  pure <| TSyntaxArray.mk alts.toArray

def checkTypeCompat: Expr → Expr → TermElabM Bool
| .forallE _ t₁ _ _, .forallE _ t₂ _ _ => do return (← Meta.isDefEq t₁ t₂) || (← checkTypeCompat t₁ t₂)
| t₁, t₂ => t₁.isSubtypeOf t₂

elab "fn " d:ident sig':optDeclSig " := " fs':functions as:altT* : command => do
  let ns ← getCurrNamespace
  withNamespace ns do
  let lhs := d.getId

  -- subtypes
  let subs ← liftTermElabM <| findSubTypes
  --logInfo m!"subs: {subs}"
  let (params', some ret') := expandOptDeclSig sig' | throwError "Function return type missing."
  let params: TSyntaxArray `Lean.Parser.Term.bracketedBinder := TSyntaxArray.mk params'.getArgs
  let ret: TSyntax `term := TSyntax.mk ret'
  let sig ← `(∀ $params:bracketedBinder* , $ret)

  --logInfo m!"params: {params} - ret: {ret} - sig: {sig}"
  let expectedType ← liftTermElabM <| elabType sig
  --logInfo m!"expected type: {expectedType}"

  let (fs, t') ← getFnVals lhs fs' subs.toList

  let body ←
    if fs.length = 1 then
       let some h := fs.head? | throwError "Summands should never be empty."
       liftTermElabM <| PrettyPrinter.delab h.body
    else
      --logInfo m!"sum type: {t'}"

      let (_, argTypes) ← typeToArgs expectedType

      --logInfo m!"argTypes: {argTypes}"

      if argTypes.isEmpty then
        throwError m!"Bogus function type {t'}"

      let some idx ← liftTermElabM <| argTypes.findIdxM? (isInductive ∘ Expr.constName!) | throwError "No inductive parameters in {t'}."
      let t := argTypes[idx]!
      --logInfo m!"t: {t}"

      let some s ← liftTermElabM <| findSuperType t | throwError "Type {t} is not a super-type."
      --logInfo m!"s: {s.type}"

      let leadingParams ← (Array.range idx).mapM (λ _ ↦ liftTermElabM <| mkFreshIdent sig)
      let v ← liftTermElabM <| mkFreshIdent sig
      let ps := leadingParams.append #[v]
      let alts: TSyntaxArray `Lean.Parser.Term.matchAlt ← liftTermElabM <| generateMatchAlts s fs leadingParams
      --logInfo m!"alts: {alts}"

      let xs := TSyntaxArray.mk (alts ++ as.raw)

      `(fun $ps* => match $v:ident with $xs:matchAlt*)

  --logInfo m!"body: {body}"

  let cmd ← `(def $d : $sig := $body)

  --logInfo m!"elaborating {cmd}"
  elabCommand cmd
