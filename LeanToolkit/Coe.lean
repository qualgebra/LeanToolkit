import LeanToolkit.Common
--import Mathlib.Data.List.Defs

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term
open Lean.Parser.Command
open Meta
open Std

-- returns two arrays: array of arg names, and a corresponding array of arg types
partial def typeToArgs'(t?: Option Expr) (ctxt:Array Name): CommandElabM (Array Name × Array Expr) := do --(TSyntaxArray `ident × TSyntaxArray `term) := do
  --logInfo m!"cntxt: {ctxt}"
  match t? with
  | some t =>
      match t with
      | .forallE n t b bi =>
          if bi.isExplicit then
            let n' ← if n.isAnonymous then mkFreshBinderName else pure n
            let t' := fillinBVars t ctxt
            --logInfo m!"abstraction: {t} {ctxt} {t'}"
            let r ← typeToArgs' (some b) (ctxt.push n)
            return (r.1.push n', r.2.push t')
          else
            typeToArgs' (some b) ctxt
      | _ => return (#[], #[])
  | none => return (#[], #[])

def typeToArgs (t?: Option Expr): CommandElabM (Array Name × Array Expr) := do
  let (a,b) ← typeToArgs' t? #[]
  return (a.reverse, b.reverse)

def genForT(t composite: Name) (ctype: Expr) (cs': List TracedConstructor): CommandElabM Unit := do
  let cs := cs'.filter (λ c ↦ c.source.toConstantVal.name == t)

  -- coercion function name
  let coe := mkIdent `coe
  let coeFnName := mkIdent (((`coe).append t).append composite)

  -- pattern matching expressions
  let mut pexprs := #[]
  for c in cs do
    --logInfo m!"constructor {c.name}: {c.type}"
    -- constructor parameters
    let (x,y) ← typeToArgs c.type
    let argIds := x.map mkIdent
    let argIds_ts' := Array.zip argIds y

    let argTerms ← argIds_ts'.mapM
      (λ (id, t') ↦ do
          --logInfo m!"names: {t'} {t}"
          if t'.constName == composite then `(($coeFnName $id)) else `($id))
    let p ← `(matchAltExpr| | $(mkIdent (c.source.name.append c.name)) $argIds:term* =>
                                    $(mkIdent <| composite.append c.name):ident $argTerms:term*)
    pexprs := pexprs.push p

  -- match expression
  let param ← mkFreshBinderName
  let m ← `(match $(mkIdent param):ident with $pexprs:matchAlt*)

  -- instance name
  let inst := mkIdent <| ((`SubType).append t).append composite

  -- subtype instance command with ceorcion function
  let (ids', ts') ← typeToArgs ctype
  let ids := ids'.map mkIdent
  let ts ← ts'.mapM (λ e ↦ liftTermElabM <| PrettyPrinter.delab e)
  let bbs: TSyntaxArray `Lean.Parser.Term.bracketedBinder ←
      (Array.zip ids ts).mapM (λ (n, t) ↦ `(bracketedBinder| ($n : $t)))

  let coeFn ← `(def $coeFnName:ident $(mkIdent param):ident := $m)

  let coeCmd ← `(instance $inst: ident $bbs:bracketedBinder* :
                    $(mkIdent `SubType)
                    ($(mkIdent t) $ids:ident*)
                    ($(mkIdent composite) $ids:ident*)
                    where $coe:ident := $coeFnName)

  --logInfo m!"elaborating {coeFn}"
  --logInfo m!"elaborating {coeCmd}"
  -- elaborate instance command
  elabCommand coeFn
  elabCommand coeCmd

def List.dedup [BEq α]: List α → List α
| [] => []
| x :: xs => if xs.contains x then dedup xs else x :: dedup xs

def genCoeInst (composite: Name) (t: Expr) (cs: List TracedConstructor): CommandElabM Unit := do
  let subtypes :=
    List.filter (not ∘ Name.isPrefixOf `hidden) <|
    List.dedup <| cs.map (ConstantVal.name ∘ InductiveVal.toConstantVal ∘ TracedConstructor.source)

  -- type args

  for s in subtypes do
    genForT s composite t cs
