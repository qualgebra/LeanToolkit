--
--  Common.lean
--
import Lean
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Meta.Inductive
import Lean.Meta.Transform

open Lean
open Elab
open Command
open Lean.Meta
open Lean.Elab.Term
open Lean.Parser.Term
open Meta
--open Std

structure TracedConstructor where
  name:        Name
  type:        Option Expr
  source:      InductiveVal
  extraParams: Nat

structure SuperType where
  type: Expr
  cs: List TracedConstructor

/-
  ⟨subtypeName, supertypeName⟩ environment extension
-/
initialize superTypesExt: EnvExtension (List SuperType) ← registerEnvExtension (return [])
initialize subfunctionExt: EnvExtension (List (Name × Name)) ← registerEnvExtension (return [])

def addSuperType (t: Expr) (cs: List TracedConstructor): MetaM Unit := do
  let env ← getEnv
  setEnv <| EnvExtension.modifyState superTypesExt env (λ rs ↦ (SuperType.mk t cs) :: rs)

def findSuperType (t: Expr): MetaM (Option SuperType) := do
  let env ← getEnv
  let s := EnvExtension.getState superTypesExt env
  s.findM? λ x ↦ do
    let r ← isDefEq x.type t
    --logInfo m!"matching {x.type} with {t} - {r}"
    return r


def getExplicitParamTypes (e: Expr): (List Expr × Expr) :=
  match e with
  | .forallE _ t b bi =>
        let (o, r) := getExplicitParamTypes b
        if bi.isImplicit then (o, r) else (t :: o, r)
  | _ => ([], e)

def isRecursiveConstructor(c: TracedConstructor): Bool :=
  match c.type with
  | none => false
  | some t =>
      let (as, r) := getExplicitParamTypes t
      as.any λ a ↦ a == r

class SubType (tSub tSuper: Type) extends Coe tSub tSuper

instance PolySubType {α: Type → Type} {β γ: Type} [i: SubType β γ] [f: Functor α] : SubType (α β) (α γ) where
  coe x := f.map i.coe x

structure Binding where
  name: Name
  type: TSyntax `term
  bi:   BinderInfo

def constantInfo2Constructor (ci': Option ConstantInfo): TermElabM Constructor := do
  match ci' with
  | some ci =>
      let cs := ci.name.components
      let n := dite (cs ≠ []) (λ ne ↦ List.getLast cs ne) (λ _ ↦ Name.anonymous)
      return (Constructor.mk n ci.type)
  | _ => throwError "not a ConstantInfo object"

def discardReturnType (e: Expr): Option Expr :=
  match e with
  | .forallE n t b bi =>
        let o := discardReturnType b
        match o with
        | some e' => some (.forallE n t e' bi)
        | none => t
  | _ => none

def fillinBVars (e: Expr) (bvars: Array Name) : Expr :=
  e.replace λ e' ↦
    match e' with
    | .bvar n =>
        if let some i := bvars[n]? then
          some <| .const i []
        else
          none
    | _ => none

def genBinder (b: Binding): TermElabM (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let t := b.type
  if b.bi.isImplicit then
    `(bracketedBinder| {$(mkIdent b.name) : $t})
  else
    `(bracketedBinder| ($(mkIdent b.name) : $t))

def genBindings: List Binding → TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder)
| []       => return #[]
| b :: bs' => do
    let h ← genBinder b
    let t ← genBindings bs'
    let all:TSyntaxArray `Lean.Parser.Term.bracketedBinder := TSyntaxArray.mk (h :: t.toList).toArray
    return all

def getInductiveVal(typ: Name): TermElabM InductiveVal := do
  let env ← getEnv
  let i := env.find? typ
  match i with
  | some j  => return j.inductiveVal!
  | _       => throwError m!"{typ} is not an inductive value."

def getTypeName: Expr → Name
| .const c _        => c
| .fvar v           => v.name
| .app f _          => getTypeName f
| .forallE _ _ b _  => getTypeName b
| _                 => Name.anonymous

def mkInstantiatedType (t: TSyntax `term): List Ident → TermElabM (TSyntax `term)
| [] => return t
| n :: ns' => do
    let r ← `($t $n)
    mkInstantiatedType r ns'

def toParams
  (e: Expr)
  (bvars: Array Name)
  (ignoreImplicit: Bool := true) :
TermElabM (List Binding × Expr) := do
  match e with
  | .forallE n t b bi => do
    let bvars' := if bi.isImplicit then bvars else bvars.insertIdx 0 n
    let b' ← toParams b bvars'
    let id := n --mkIdent n --(← mkFreshUserName `x)
    let t' ← PrettyPrinter.delab (fillinBVars t bvars)
    let r :=
      if ignoreImplicit && bi.isImplicit then
        b'
      else
        ⟨ ⟨id, t', bi⟩ :: b'.fst, fillinBVars b bvars'⟩
    return r
  | _ => return ⟨ [], fillinBVars e bvars⟩
