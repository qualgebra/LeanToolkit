--
-- Kleene K3 logic (logic of indeterminacy)
--
import AR.Tools.Compose
import Lean

--class TermOps (α: Type) where
--  countNodes : α → Nat
--  positiveSize : ∀ x: α, countNodes x > 0

namespace Boolean

inductive Term
| T
| F

def countNodes (t: Term): Nat :=
1 + match t with
| .T => 1
| .F => 1

#check countNodes.eq_unfold

theorem positiveSize: ∀x: Term, countNodes x > 0 :=
by intros x; cases x <;> simp[countNodes]

--instance (α: Σ T, TermOps T): TermOps (BTerm α) where
--  countNodes := _countNodes α
--  positiveSize := _positiveSize α

end Boolean

/-
namespace Indet

inductive Term
| I

def countNodes(t: Term): Nat :=
1+ match t with
| .I => 1

theorem eq (t: Term): t = t := by rfl

end Indet
-/

namespace Ops

inductive Term
| Neg (t: Term)
| And (t₁ t₂: Term)
| Or  (t₁ t₂: Term)
| Imp (t₁ t₂: Term)

def countNodes: Term → Nat
| .Neg t      => 1 + countNodes t
| .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
| .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
| .Imp t₁ t₂  => 1 + countNodes t₁ + countNodes t₂

theorem positiveSize: ∀x: Term, countNodes x > 0 :=
by
  intros x
  cases x with
  | Neg x   => simp[countNodes]; rw [Nat.one_add]; simp[Nat.zero_lt_succ]
  | And x y => simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
  | Or x y  => simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
  | Imp x y => simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]

#print positiveSize
--instance TTOps (α: Σ T, TermOps T): TermOps (Term α) where
--  countNodes := _countNodes α
--  positiveSize := _positiveSize α

end Ops

namespace BooleanLogic
inductive Term := Boolean.Term |+ Ops.Term
#print Term

def countNodes(t: Term): Nat :=
  match t with
  | .T        => 1
  | .F        => 1
  | .Neg t    => 1 + (countNodes t)
  | .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
  | .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
  | .Imp t₁ t₂  => 1 + countNodes t₁ + (countNodes t₂)

#print Ops.countNodes.eq_unfold
--theorem positiveSize: ∀x: Term, countNodes x > 0 :=
--by
--  intros x; cases x <;> first | try apply Boolean.positiveSize | try apply Ops.positiveSize
/-
  intros x
  induction x with
  | T => simp[countNodes]
  | F => simp[countNodes]
  | Neg x   => simp[countNodes]; rw [Nat.one_add]; simp[Nat.zero_lt_succ]
  | And x y => simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
  | Or x y  => simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
  | Imp x y ih₁ ih₂ => simp[countNodes]; apply Nat.lt_add_left; exact ih₂
-/
/-
def countNodes: Term → Nat
| Term.T => Boolean.countNodes Term.T
| Term.F => Boolean.countNodes Term.F
| Term.I => Indet.countNodes Term.I
-/


/-
fn countNodes := Boolean.countNodes + Indet.countNodes + Ops.countNodes
#print Term
def countNodes (t: Term):  Nat :=
  match t with
  | .T => Boolean.countNodes .T
  | .F => Boolean.countNodes .F
  | .I => Indet.countNodes .I
  | .Neg t => countNodes_Ops (.Neg t) --Term → Term
where
  countNodes_Ops (t: Term) :=
  match t with
  | .Neg t      => 1 + countNodes t
  | .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
  | .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
  | .Imp t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
  -/
--Term.And : Term → Term → Term
--Term.Or : Term → Term → Term
--Term.Imp : Term → Term → Term

--theorem eq (t: Term): t = t := Boolean.eq
--by
--  cases t with --first | apply Boolean.eq | apply Indet.eq | apply Ops.eq
--  | T => apply Boolean.eq ↑.T
--  | F => apply Boolean.eq
--  | I => apply Indet.eq

 --<;> first | apply Boolean.eq | apply Indet.eq | apply Ops.eq

--inductive countNodes := Boolean.countNodes + Indet.countNodes
--| .T => Boolean.countNodes .T
--| .F => Boolean.countNodes .F
--| .I => Indet.countNodes .I
--| .Neg t => Ops.countNodes (.Neg t)



--<;> Boolean.countNodes | Ops.countNodes

--| .T => countNodes .T

--BooleanLogic.Term.F : Term
--BooleanLogic.Term.Neg : Term → Term
--BooleanLogic.Term.And : Term → Term → Term
--BooleanLogic.Term.Or : Term → Term → Term
--BooleanLogic.Term.Imp : Term → Term → Term
end BooleanLogic

namespace K3Logic

inductive Term := Boolean.Term |+ Indet.Term |+ Ops.Term
#print Term
end K3Logic

namespace baseline
inductive Term
| T | F | I
| Neg (t: Term)
| And (t₁ t₂: Term)
| Or  (t₁ t₂: Term)
| Imp (t₁ t₂: Term)

def countNodes: Term→ Nat
| .T          => 1
| .F          => 1
| .I          => 1
| .Neg t      => 1 + countNodes t
| .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
| .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
| .Imp t₁ t₂  => 1 + countNodes t₁ + countNodes t₂

namespace Boolean

inductive Term
| T
| F

def countNodes: Term→ Nat
| .T          => 1
| .F          => 1

end Boolean

namespace Indet

inductive Term
| I

def countNodes: Term → Nat
| .I          => 1

end Indet

namespace Ops

inductive Term
| Neg (t: Term)
| And (t₁ t₂: Term)
| Or  (t₁ t₂: Term)
| Imp (t₁ t₂: Term)

def countNodes: Term→ Nat
| .Neg t      => 1 + countNodes t
| .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
| .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
| .Imp t₁ t₂  => 1 + countNodes t₁ + countNodes t₂

end Ops
--
-- def Lean.Meta.getConstUnfoldEqnFor? (declName : Name) :
--MetaM (Option Name)

--Returns the "const unfold" theorem (f.eq_unfold) for the given declaration. This is not extensible, and always builds on the unfold theorem (f.eq_def).

#check countNodes.eq_unfold
def x := Term.T
#print x

#check Term.brecOn
#check Term.below
#print Term.below
#check Term.rec

#print countNodes
end baseline
