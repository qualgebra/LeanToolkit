/-
  Syntax.lean

  Exntended syntax for type and function sums.
-/
import LeanToolkit.Common
import LeanToolkit.TypeSum
import LeanToolkit.FnSum
import LeanToolkit.Coe

open Lean
open Elab
open Command
--open Lean.Meta
open Lean.Elab.Term
--open Lean.Parser.Term
open Lean.Parser.Command
--open Meta
--open Std

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

/-
  resolveTypeName

  resolve a type name given current namespace context
-/
private def resolveTypeName (n: Name): TermElabM (List Name) := do
  let ns ← Lean.resolveGlobalName n
  --logInfo m!"resolved names: {ns}"
  let result ← ns.findM? λ (n, _) ↦ isInductive n
  if result.isNone then
    throwError m!"{n} is not an inductive type"
  else
    return result.toList.map Prod.fst

/-
  helper function for turning the constituent type names
  into a list of names
-/
private partial def getTypeVals': TSyntax `types → TermElabM (List Name)
| `(types| $i:ident) => do
    resolveTypeName i.getId
      -- let ns ← Lean.resolveGlobalName i.getId
      -- logInfo m!"resolved names: {ns}"
      -- if (← isInductive i.getId) then
      --   return [i.getId]
      -- else
      --   throwError m!"{i.getId} is not inductive."
| `(types| $l:types |+ $r:types) => do
      let x ← getTypeVals' l
      let y ← getTypeVals' r
       return x ++ y
| _ => return  []

def getTypeVals(cs: TSyntax `types): TermElabM (List InductiveVal) := do
  --let env ← getEnv
  let ns ← getTypeVals' cs
  let ns' := List.eraseDups ns
  ns'.mapM getInductiveVal

--
--  elaborator for type sum syntax
--
elab "inductive " d:ident sig':optDeclSig " := " cs':types explicitCs: ctor* : command => do
  let mut cs := cs'
  let lhs := d.getId

  let (_, optSig) := expandOptDeclSig sig'
  let expectedType ← optSig.bindM
    (λ s ↦ do pure <| some (← liftTermElabM <| elabType s))

  --logInfo m!"expected type: {expectedType}"
  let ts ← liftTermElabM <| getTypeVals cs

  let ⟨cObjs, e, _⟩ ← liftTermElabM <| typeSumImp ts expectedType lhs
  let cStx ← cObjs.mapM (λ c ↦ do
        match c.type with
        | some t' =>
            let t ← liftTermElabM <| PrettyPrinter.delab t'
            `(ctor| |$(mkIdent c.name):ident : $t:term)
        | none => `(ctor| |$(mkIdent c.name):ident))

  let cStx := cStx.toArray ++ explicitCs
  let e' ← liftTermElabM <| PrettyPrinter.delab e
  let cmd ← `(inductive $(mkIdent lhs) : $e' $cStx:ctor*)
  --logInfo m!"elaborating {cmd}"
  elabCommand cmd

  --let s ← liftTermElabM <| getInductiveVal lhs
  --let propType ← liftTermElabM <| isPropFormerType s.type

  --if !propType then
  genCoeInst lhs e cObjs
    --for t in ts do
      --let t ← liftTermElabM <| getInductiveVal t.name
      --upCoe s t
      --downCoe t s

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

def getFnVals (lhs: Name) (stx: TSyntax `functions) (subs: List (Name × Name)): CommandElabM (List Fn) := do
  let fs' ← liftTermElabM <| getFnVals' stx
  let fs := List.eraseDups fs'
  logInfo m!"functions: {fs}"
  --let env ← getEnv

  fs.forM λ f ↦
    addFnPair f lhs

  fs.mapM λ f' ↦ do
    let o' ← liftTermElabM <| Lean.Meta.getUnfoldEqnFor? f'
    let o := match o' with
             | some x => x
             | _ => f'

    let alts ← liftTermElabM <| extractAlts f' ((← getConstInfo o).value!) subs

    logInfo m!"found alts: {alts}"
    let t := (← getConstInfo f').type

    return (Fn.mk f' t ((← getConstInfo f').value!) alts)

/-
  elaborator for type sum syntax
-/
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
