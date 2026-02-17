import CaseStudy.Boolean
import CaseStudy.Nat
import CaseStudy.STLC
import LeanToolkit

inductive T := Boolean.T |+ Nat.T |+ STLC.T

/--
info: inductive T : Type
number of parameters: 0
constructors:
T.Bool : T
T.N : T
T.Fn : T → T → T
-/
#guard_msgs in
#print T


inductive Term := Boolean.Term |+ Nat.Term |+ STLC.Term
| isZero (t: Term)

/--
info: inductive Term : Type
number of parameters: 0
constructors:
Term.True : Term
Term.False : Term
Term.If : Term → Term → Term → Term
Term.Zero : Term
Term.Succ : Term → Term
Term.Pred : Term → Term
Term.V : STLC.Var → Term
Term.Abs : STLC.Var → T → Term → Term
Term.App : Term → Term → Term
Term.isZero : Term → Term
-/
#guard_msgs in
#print Term

fn countNodes: Term → Nat := Boolean.countNodes |+ Nat.countNodes |+ STLC.countNodes
| Term.isZero t => 1 + countNodes t
| Term.App a b => 1 + countNodes a  + countNodes b
| Term.Abs _ _ b => 2 + countNodes b
| Term.Pred t => 1 + countNodes t
| Term.Succ t => 1 + countNodes t
| Term.If c t e => 1 + countNodes c + countNodes t + countNodes e

/--
info: def countNodes : Term → Nat :=
fun x =>
  Term.brecOn x fun x f =>
    (match (motive := (x : Term) → Term.below x → Nat) x with
      | Term.True => fun x => Boolean.countNodes Boolean.Term.True
      | Term.False => fun x => Boolean.countNodes Boolean.Term.False
      | Term.Zero => fun x => Nat.countNodes Nat.Term.Zero
      | Term.V x => fun x_1 => STLC.countNodes (STLC.Term.V x)
      | t.isZero => fun x => 1 + x.1
      | a.App b => fun x => 1 + x.1.1 + x.2.1
      | Term.Abs a a_1 b => fun x => 2 + x.1
      | t.Pred => fun x => 1 + x.1
      | t.Succ => fun x => 1 + x.1
      | c.If t e => fun x => 1 + x.1.1 + x.2.1.1 + x.2.2.1)
      f
-/
#guard_msgs in
#print countNodes

inductive Val := Boolean.Val |+ Nat.Val |+ STLC.Val

/--
info: inductive Val : Term → Prop
number of parameters: 0
constructors:
Val.T : Val Term.True
Val.F : Val Term.False
Val.Z : Val Term.Zero
Val.S : ∀ (v : Term), Val v → Val v.Succ
Val.A : ∀ {t : Term} (x : STLC.Var) (τ : T) (a : Term), Val (Term.Abs x τ t)
-/
#guard_msgs in
#print Val

-- def nonEmpty(t: Term): countNodes t > 0 :=
--   match t with
--   | .True => Boolean.nonEmpty .True
--   | .False => Boolean.nonEmpty .False
--   | .Zero => Nat.nonEmpty .Zero
--   | .V v => STLC.nonEmpty (.V v)
--   | .If c t e => by simp[countNodes, Nat.succ_add]
--   | .Succ t => by simp[countNodes, Nat.succ_add]
--   | .Pred t => by simp[countNodes, Nat.succ_add]
--   | .Abs v τ t => by simp[countNodes]; apply Nat.lt_add_left; apply nonEmpty t
--   | .App t₁ t₂ => by simp[countNodes, Nat.succ_add]
--   | .isZero t => by simp[countNodes, Nat.succ_add]

fn notEmpty (t: Term) : countNodes t > 0 := Boolean.notEmpty |+ Nat.notEmpty |+ STLC.notEmpty
| .If c t e   => by simp[countNodes, Nat.succ_add]
| .Succ t     => by simp[countNodes, Nat.succ_add]
| .Pred t     => by simp[countNodes, Nat.succ_add]
| .Abs v τ t  => by simp[countNodes]; apply Nat.lt_add_left; apply notEmpty t
| .App t₁ t₂  => by simp[countNodes, Nat.succ_add]
| .isZero t   => by simp[countNodes, Nat.succ_add]

/--
info:
def notEmpty : ∀ (t : Term), countNodes t > 0 :=
fun x =>
  Term.brecOn x fun x f =>
    (match (motive := ∀ (x : Term) (x_1 : Term.below x), countNodes x > 0) x with
      | Term.True => fun x => Boolean.notEmpty Boolean.Term.True
      | Term.False => fun x => Boolean.notEmpty Boolean.Term.False
      | Term.Zero => fun x => Nat.notEmpty Nat.Term.Zero
      | Term.V x => fun x_1 => STLC.notEmpty (STLC.Term.V x)
      | c.If t e => fun x =>
        of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg GT.gt
                  (Eq.trans
                    (congrFun'
                      (congrArg HAdd.hAdd
                        (Eq.trans
                          (congrFun'
                            (congrArg HAdd.hAdd
                              (Eq.trans (Nat.succ_add 0 (countNodes c))
                                (congrArg Nat.succ (Nat.zero_add (countNodes c)))))
                            (countNodes t))
                          (Nat.succ_add (countNodes c) (countNodes t))))
                      (countNodes e))
                    (Nat.succ_add (countNodes c + countNodes t) (countNodes e))))
                0)
              gt_iff_lt._simp_1)
            (Nat.zero_lt_succ._simp_1 (countNodes c + countNodes t + countNodes e)))
      | t.Succ => fun x =>
        of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg GT.gt
                  (Eq.trans (Nat.succ_add 0 (countNodes t)) (congrArg Nat.succ (Nat.zero_add (countNodes t)))))
                0)
              gt_iff_lt._simp_1)
            (Nat.zero_lt_succ._simp_1 (countNodes t)))
      | t.Pred => fun x =>
        of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg GT.gt
                  (Eq.trans (Nat.succ_add 0 (countNodes t)) (congrArg Nat.succ (Nat.zero_add (countNodes t)))))
                0)
              gt_iff_lt._simp_1)
            (Nat.zero_lt_succ._simp_1 (countNodes t)))
      | Term.Abs v τ t => fun x => Eq.mpr (id gt_iff_lt._simp_1) (Nat.lt_add_left 2 x.1)
      | t₁.App t₂ => fun x =>
        of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg GT.gt
                  (Eq.trans
                    (congrFun'
                      (congrArg HAdd.hAdd
                        (Eq.trans (Nat.succ_add 0 (countNodes t₁)) (congrArg Nat.succ (Nat.zero_add (countNodes t₁)))))
                      (countNodes t₂))
                    (Nat.succ_add (countNodes t₁) (countNodes t₂))))
                0)
              gt_iff_lt._simp_1)
            (Nat.zero_lt_succ._simp_1 (countNodes t₁ + countNodes t₂)))
      | t.isZero => fun x =>
        of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg GT.gt
                  (Eq.trans (Nat.succ_add 0 (countNodes t)) (congrArg Nat.succ (Nat.zero_add (countNodes t)))))
                0)
              gt_iff_lt._simp_1)
            (Nat.zero_lt_succ._simp_1 (countNodes t))))
      f
-/
#guard_msgs in
#print notEmpty

/-
def Context := STLC.Var → T

instance: SubType STLC.Context Context where
  coe f := λ x ↦ f x
#check STLC.augment
fn augment: STLC.Context → STLC.Var → STLC.T → STLC.Context := STLC.augment
#check STLC.augment
#print STLC.augment
#check augment
#print augment
-/

def Context := STLC.Var → T

instance: SubType STLC.Context Context where
  coe f := λ x ↦ f x

fn augment: Context → STLC.Var → T → Context := STLC.augment

/--
info: def augment : Context → STLC.Var → T → Context :=
fun Γ x τ v => if v = x then τ else Γ v
-/
#guard_msgs in
#print augment

inductive TRel: Context → Term → T → Prop := Boolean.TRel |+ Nat.TRel |+ STLC.TRel
| iz: TRel Γ t T.N → TRel Γ (Term.isZero t) T.Bool

/--
info: inductive TRel : Context → Term → T → Prop
number of parameters: 0
constructors:
TRel.TT : ∀ {_ : Context}, TRel _ Term.True T.Bool
TRel.FF : ∀ {_ : Context}, TRel _ Term.False T.Bool
TRel.If : ∀ {_ : Context} {c t₁ : Term} {τ : T} {t₂ : Term},
  TRel _ c T.Bool → TRel _ t₁ τ → TRel _ t₂ τ → TRel _ (c.If t₁ t₂) τ
TRel.Z : ∀ {_ : Context}, TRel _ Term.Zero T.N
TRel.S : ∀ {_ : Context} {t : Term}, TRel _ t T.N → TRel _ t.Succ T.N
TRel.P : ∀ {_ : Context} {t : Term}, TRel _ t T.N → TRel _ t.Pred T.N
TRel.V : ∀ {Γ : Context} (x : STLC.Var) (τ : T), Γ x = τ → TRel Γ (Term.V x) τ
TRel.Abs : ∀ {Γ : Context} (x : STLC.Var) (b : Term) (τ₁ τ₂ : T),
  TRel (augment Γ x τ₁) b τ₂ → TRel Γ (Term.Abs x τ₁ b) (τ₁.Fn τ₂)
TRel.App : ∀ {Γ : Context} (t₁ t₂ : Term) (τ₁ τ₂ : T), TRel Γ t₁ (τ₁.Fn τ₂) → TRel Γ t₂ τ₁ → TRel Γ (t₁.App t₂) τ₂
TRel.iz : ∀ {Γ : Context} {t : Term}, TRel Γ t T.N → TRel Γ t.isZero T.Bool
-/
#guard_msgs in
#print TRel
