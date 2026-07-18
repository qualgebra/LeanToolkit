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

def genCoeDepInst (composite t ctorName: Name) (ctr: TracedConstructor) (ctor rhs: TSyntax `term)
  (args: TSyntaxArray `Lean.Parser.Term.bracketedBinder) : CommandElabM Unit := do

  let instName := mkIdent <| (((`coeDep).append composite).append ctorName).append t
  --let idComposite := mkIdent composite
  --let id_t := mkIdent t
  let ctorT' := if h: ctr.type.isSome then ctr.type.get h else mkConst composite []
  let t_ctorT ← liftTermElabM <| forallTelescope ctorT' λ _ ctorT ↦ do
    let t_ctorT ← PrettyPrinter.delab ctorT
    let subt := ctorT.replace λ e ↦ if e.isConstOf composite then mkConst t else none
    let t_subt ← PrettyPrinter.delab subt
    let e ← `(CoeDep $t_ctorT $ctor $t_subt)
    return e

  --logInfo m!"t_ctorT: {t_ctorT}"
  --let t_ctorT ← liftTermElabM <| PrettyPrinter.delab ctorT
  --let subt := ctorT.replace λ e ↦ if e.isConstOf composite then mkConst t else none
  --let t_subt ← liftTermElabM <| PrettyPrinter.delab subt
  let coe := mkIdent `coe
  let cmd ← `(instance $instName:ident $args:bracketedBinder* : $t_ctorT
              where $coe:ident := $rhs)
  --logInfo m!"elaborating {cmd}"
  elabCommand cmd

def genForT(t composite: Name) (ctype: Expr) (cs': List TracedConstructor): CommandElabM Unit := do
  -- calculate type indices
  let (ids', ts') ← typeToArgs ctype
  let ids := ids'.map mkIdent
  let ts ← ts'.mapM (λ e ↦ liftTermElabM <| PrettyPrinter.delab e)
  let bbs: TSyntaxArray `Lean.Parser.Term.bracketedBinder ←
      (Array.zip ids ts).mapM (λ (n, t) ↦ `(bracketedBinder| {$n : $t}))

  let cs := cs'.filter (λ c ↦ c.source.toConstantVal.name == t)

  -- coercion function name
  let coe := mkIdent `coe
  let coeFnName := mkIdent (((`coe).append t).append composite)

  let tSub ← liftTermElabM <|
    PrettyPrinter.delab (mkAppN (Expr.fvar (FVarId.mk t)) (ids'.map (Expr.fvar ∘ FVarId.mk)))
  let tSuper ← liftTermElabM <|
    PrettyPrinter.delab (mkAppN (Expr.fvar (FVarId.mk composite)) (ids'.map (Expr.fvar ∘ FVarId.mk)))
  --logInfo m!"tSub: {tSub} - tSuper: {tSuper}"

  -- pattern matching expressions
  let mut pexprs := #[]
  for c in cs do
    --logInfo m!"constructor {c.name}: {c.type}"
    -- constructor parameters
    let (x,y) ← typeToArgs c.type
    let argIds := x.map mkIdent
    let argIds_ts' := Array.zip argIds y

    let lhs ← `($(mkIdent <| c.source.name.append c.name):ident $argIds:term*)
    --logInfo m!"type: {t}"
    --logInfo m!"composite: {composite}"

    --logInfo m!"isRecursiveConstructor: {c.name} {c.source.name} : {c.type}"
    if !isRecursiveConstructor c then
      let consWithParams ← `($(mkIdent <| composite.append c.name):ident $argIds:term*)
      let consArgs: TSyntaxArray `Lean.Parser.Term.bracketedBinder ← argIds_ts'.mapM λ (i, t) ↦ do
        let t' ← liftTermElabM <| PrettyPrinter.delab t
        `(bracketedBinder| {$i:ident : $t'})
      genCoeDepInst composite t c.name c consWithParams lhs (/-bbs.append-/ consArgs)

    let argTerms ← argIds_ts'.mapM
      (λ (id, t') ↦ do
          --logInfo m!"names: {t'} {t}"
          if t'.isAppOf composite then `(($coeFnName $id)) else `($id))

    let rhs ← `($(mkIdent <| composite.append c.name):ident $argTerms:term*)
    let p ← `(matchAltExpr| | $lhs => $rhs)
    pexprs := pexprs.push p


  -- match expression
  let param ← mkFreshBinderName
  let m ← `(match $(mkIdent param):ident with $pexprs:matchAlt*)

  -- instance name
  let inst := mkIdent <| ((`SubType).append t).append composite

  -- subtype instance command with ceorcion function

  let indices' ← ((Array.zip ids ts).mapM λ (id, t) ↦ do `(bracketedBinder| {$id:ident : $t}))

  let indices'' := indices'.push (← `(bracketedBinder| ($(mkIdent param):ident : $tSub)))

  let indices:TSyntaxArray `Lean.Parser.Term.bracketedBinder := TSyntaxArray.mk indices''

  let sig ← `(optDeclSig| $indices:bracketedBinder* : $tSuper)
  --logInfo m!"sig: {sig}"

  let coeFn ← `(def $coeFnName:ident $sig := $m)

  let coeCmd ← `(instance $inst: ident $bbs:bracketedBinder* :
                    $(mkIdent `SubType)
                    ($tSub)
                    ($tSuper)
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
  --logInfo m!"t: {t}"

  for s in subtypes do
    genForT s composite t cs
