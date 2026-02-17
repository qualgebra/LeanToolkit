--
-- Kleene K3 logic (logic of indeterminacy)
--
import LeanToolkit

set_option pp.fieldNotation.generalized false

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

theorem positiveSize: ∀x: Term, countNodes x > 0 :=
by intros x; cases x <;> simp[countNodes]

end Boolean


namespace Indet

inductive Term
| I

def countNodes(t: Term): Nat :=
1+ match t with
| .I => 1

theorem positiveSize (t: Term): countNodes t > 0  := by simp[countNodes]

end Indet

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

end Ops

--namespace BooleanLogic
inductive Term := Boolean.Term |+ Ops.Term
/--
info:
inductive Term : Type
number of parameters: 0
constructors:
Term.T : Term
Term.F : Term
Term.Neg : Term → Term
Term.And : Term → Term → Term
Term.Or : Term → Term → Term
Term.Imp : Term → Term → Term
-/
#guard_msgs in
#print Term

fn countNodes: Term → Nat := Boolean.countNodes |+ Ops.countNodes
| .Neg t    => 1 + (countNodes t)
| .And t₁ t₂  => 1 + countNodes t₁ + countNodes t₂
| .Or t₁ t₂   => 1 + countNodes t₁ + countNodes t₂
| .Imp t₁ t₂  => 1 + countNodes t₁ + (countNodes t₂)

/--
info:
def countNodes : Term → Nat :=
fun x =>
  Term.brecOn x fun x f =>
    (match (motive := (x : Term) → Term.below x → Nat) x with
      | Term.T => fun x => Boolean.countNodes Boolean.Term.T
      | Term.F => fun x => Boolean.countNodes Boolean.Term.F
      | Term.Neg t => fun x => 1 + x.1
      | Term.And t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | Term.Or t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | Term.Imp t₁ t₂ => fun x => 1 + x.1.1 + x.2.1)
      f
-/
#guard_msgs in
#print countNodes

fn positiveSize(x: Term): countNodes x > 0 := Boolean.positiveSize |+ Ops.positiveSize
| .Neg x   => by simp[countNodes]; rw [Nat.one_add]; simp[Nat.zero_lt_succ]
| .And x y => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
| .Or x y  => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
| .Imp x y => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]

/--
info:
def positiveSize : ∀ (x : Term), countNodes x > 0 :=
fun x =>
  match x with
  | Term.T => Boolean.positiveSize Boolean.Term.T
  | Term.F => Boolean.positiveSize Boolean.Term.F
  | Term.Neg x =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.one_add (countNodes x))))
        (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x))))
  | Term.And x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
  | Term.Or x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
  | Term.Imp x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
-/
#guard_msgs in
#print positiveSize

inductive K3Term := Boolean.Term |+ Indet.Term |+ Ops.Term

/--
info:
inductive K3Term : Type
number of parameters: 0
constructors:
K3Term.T : K3Term
K3Term.F : K3Term
K3Term.I : K3Term
K3Term.Neg : K3Term → K3Term
K3Term.And : K3Term → K3Term → K3Term
K3Term.Or : K3Term → K3Term → K3Term
K3Term.Imp : K3Term → K3Term → K3Term
-/
#guard_msgs in
#print K3Term

fn K3countNodes: K3Term → Nat := Boolean.countNodes |+ Indet.countNodes |+ Ops.countNodes
| .Neg t    => 1 + (K3countNodes t)
| .And t₁ t₂  => 1 + K3countNodes t₁ + K3countNodes t₂
| .Or t₁ t₂   => 1 + K3countNodes t₁ + K3countNodes t₂
| .Imp t₁ t₂  => 1 + K3countNodes t₁ + (K3countNodes t₂)

/--
info:
def K3countNodes : K3Term → Nat :=
fun x =>
  K3Term.brecOn x fun x f =>
    (match (motive := (x : K3Term) → K3Term.below x → Nat) x with
      | K3Term.T => fun x => Boolean.countNodes Boolean.Term.T
      | K3Term.F => fun x => Boolean.countNodes Boolean.Term.F
      | K3Term.I => fun x => Indet.countNodes Indet.Term.I
      | K3Term.Neg t => fun x => 1 + x.1
      | K3Term.And t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | K3Term.Or t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | K3Term.Imp t₁ t₂ => fun x => 1 + x.1.1 + x.2.1)
      f
-/
#guard_msgs in
#print K3countNodes

fnRec K3countNodes': K3Term → Nat := Boolean.countNodes |+ Indet.countNodes |+ Ops.countNodes

/--
info:
def K3countNodes' : K3Term → Nat :=
fun x =>
  K3Term.brecOn x fun x f =>
    (match (motive := (x : K3Term) → K3Term.below x → Nat) x with
      | K3Term.T => fun x => Boolean.countNodes Boolean.Term.T
      | K3Term.F => fun x => Boolean.countNodes Boolean.Term.F
      | K3Term.I => fun x => Indet.countNodes Indet.Term.I
      | K3Term.Neg t => fun x => 1 + x.1
      | K3Term.And t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | K3Term.Or t₁ t₂ => fun x => 1 + x.1.1 + x.2.1
      | K3Term.Imp t₁ t₂ => fun x => 1 + x.1.1 + x.2.1)
      f
-/
#guard_msgs in
#print K3countNodes'

fn K3positiveSize(x: Term): countNodes x > 0 := Boolean.positiveSize |+ Indet.positiveSize |+ Ops.positiveSize
| .Neg x   => by simp[countNodes]; rw [Nat.one_add]; simp[Nat.zero_lt_succ]
| .And x y => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
| .Or x y  => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]
| .Imp x y => by simp[countNodes]; rw [Nat.one_add, Nat.succ_add]; simp[Nat.zero_lt_succ]

/--
info:
def K3positiveSize : ∀ (x : Term), countNodes x > 0 :=
fun x =>
  match x with
  | Term.T => Boolean.positiveSize Boolean.Term.T
  | Term.F => Boolean.positiveSize Boolean.Term.F
  | Term.Neg x =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.one_add (countNodes x))))
        (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x))))
  | Term.And x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
  | Term.Or x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
  | Term.Imp x y =>
    Eq.mpr (id gt_iff_lt._simp_1)
      (Eq.mpr (id (congrArg (fun _a => 0 < _a + countNodes y) (Nat.one_add (countNodes x))))
        (Eq.mpr (id (congrArg (fun _a => 0 < _a) (Nat.succ_add (countNodes x) (countNodes y))))
          (of_eq_true (Nat.zero_lt_succ._simp_1 (countNodes x + countNodes y)))))
-/
#guard_msgs in
#print K3positiveSize
