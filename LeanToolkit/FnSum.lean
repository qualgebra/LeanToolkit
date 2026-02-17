--
--  FnSum.lean
--
import LeanToolkit.Common
import LeanToolkit.Subtype
import LeanToolkit.Coe

open Lean Lean.Meta
open Elab
open Command
open Lean.Elab.Term
--open Lean.Parser.Term
open Lean.Parser.Command

--open Lean Elab Command Lean.Meta Lean.Elab.Term
--open Lean.Parser.Term
--open Lean.Parser.Command
--open Meta
--open Std

-- namespace AR.Tools.Compose.FnSum

set_option pp.fieldNotation false

structure Fn where
  name: Name
  type: Expr
  body: Expr
  alts: Array (Syntax × Syntax)

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

    let alts' ← liftTermElabM <| extractAlts f' ((← getConstInfo o).value!) subs
    let alts ← alts'.mapM λ x ↦ do
      return (((x.getArg 1).getArg 0).getArg 0, x.getArg 3)

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

def abstractConstructor(c: TracedConstructor): MetaM (TSyntax `term × TSyntaxArray `ident) := do
  let n := if c.type.isSome then paramCount c.type.get! else 0
  let mut ps: List (TSyntax `term) := []
  for _ in List.range n do
    ps := mkIdent (← mkFreshBinderName) :: ps
  let x ← `(.$(mkIdent c.name) $(ps.toArray):term*)
  let y: TSyntaxArray `ident :=  TSyntaxArray.mk ps.toArray
  return (x, y)

-- def unpack (stx: TSyntax `term): TSyntax `term :=
--   stx.raw.modifyArgs
--     λ args ↦ args.map
--       λ a ↦ let cs := a.getId.componentsRev
--             cs.tail.foldr
--               λ c cs ↦ `(term| $(mkIdent c) $cs*)
--            `(term| $cs.head)
def findRhs (fn: Fn) (ctor: Name): TermElabM (TSyntax `term × TSyntax `term) := do
  let some r ← fn.alts.findM? λ a ↦ do
          let r := (a.1.getArg 0).getId
          let x := r.componentsRev.head! == ctor
          --logInfo m!"matching against {r}"
          return x --(x.getId == ctor)
    | throwError "constructor {ctor} not found in {fn.name}"
  return (TSyntax.mk r.1, TSyntax.mk r.2)

def generateMatchAlts(rec: Bool) (s: SuperType) (fns: List Fn) (ps: TSyntaxArray `ident): TermElabM (TSyntaxArray `Lean.Parser.Term.matchAlt) := do
  let cs := if rec then s.cs else s.cs.filter (not ∘ isRecursiveConstructor)
  let alts ← cs.mapM λ c ↦ do
    --logInfo m!"constructor: {c.name} - {s.type}"
    --let cnsTerm := mkIdent c.name
    let some f ← findSubFunction fns c.source | throwError "Function with matching source not found."
    let (lhs,_) ← abstractConstructor c
    --let mut rhs: TSyntax `term ← `(none)
    if isRecursiveConstructor c then
      --let o := mkIdent `Ops.Term.Neg
      --let stx ← `(∀ x', ($(mkIdent f.name) ($o x')))
      --let e ← elabTerm stx none
      --let e' ← forallTelescope e λ _ e ↦ Lean.Core.betaReduce e
      --let e' ←  Lean.Core.betaReduce e
      --logInfo m!"{stx} - beta reduced: {e} - {e'}"
      --let p ← elabTerm lhs none
      --let e := Expr.beta (Expr.const f.name []) #[p]
      let (lh, rh) ← findRhs f c.name --PrettyPrinter.delab e'
      --logInfo m!"lhs-rhs: {lh} => {rh}"
      `(matchAltExpr| | $lh => $rh)
    else
      let rhs ← `($(mkIdent f.name) $ps* ($lhs))
      `(matchAltExpr| | $lhs => $rhs)

  pure <| TSyntaxArray.mk alts.toArray

def checkTypeCompat: Expr → Expr → TermElabM Bool
| .forallE _ t₁ _ _, .forallE _ t₂ _ _ => do return (← Meta.isDefEq t₁ t₂) || (← checkTypeCompat t₁ t₂)
| t₁, t₂ => t₁.isSubtypeOf t₂

def elabFn (rec:Bool) (d:TSyntax `ident) (sig':TSyntax `Lean.Parser.Command.optDeclSig) (fs':TSyntax `functions) (as:TSyntaxArray `altT) : CommandElabM Unit := do
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
      let alts: TSyntaxArray `Lean.Parser.Term.matchAlt ← liftTermElabM <| generateMatchAlts rec s fs leadingParams
      --logInfo m!"alts: {alts}"

      let xs := TSyntaxArray.mk (alts ++ as.raw)

      `(fun $ps* => match $v:ident with $xs:matchAlt*)

  --logInfo m!"body: {body}"

  let cmd ← `(def $d : $sig := $body)

  --logInfo m!"elaborating {cmd}"
  elabCommand cmd

elab "fn " d:ident sig:optDeclSig " := " fs:functions as:altT* : command => elabFn false d sig fs as
elab "fnRec " d:ident sig:optDeclSig " := " fs:functions as:altT* : command => elabFn true d sig fs as
