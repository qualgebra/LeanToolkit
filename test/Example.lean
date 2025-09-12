import LeanToolkit

--
-- Boolean
--
namespace Boolean

inductive T where
| Bool

inductive Term where
| True | False
| If (c t₁ t₂: Term)

def countNodes: Term → Nat
| .True => 1
| .False => 1
| .If c t₁ t₂ => 1 + countNodes c + countNodes t₁ + countNodes t₂

inductive Val: Term → Prop
| T: Val .True | F: Val .False

inductive TRel: Term → T → Prop
| TT: TRel .True .Bool
| FF: TRel .False .Bool
| If: TRel c .Bool → TRel t₁ τ → TRel t₂ τ → TRel (.If c t₁ t₂) τ

theorem countNodes_pos: ∀ (t:Term), countNodes t > 0 := by
  intros t;
  induction t with
  | True => simp[countNodes]
  | False => simp[countNodes]
  | If c t₁ t₂ c_ih t₁_ih t₂_ih => simp[countNodes]; simp[Nat.add_assoc]; simp[Nat.add_comm 1 _]

end Boolean

--
-- Nat
--
namespace Nat

inductive T where
| N

inductive Term where
| Zero
| Succ (t: Term)
| Pred (t: Term)

def countNodes: Term → Nat
| .Zero => 1
| .Succ t => 1 + countNodes t
| .Pred t => 1 + countNodes t

inductive Val: Term → Prop
| Z: Val .Zero
| S (v: Term): Val v → Val (.Succ v)

inductive TRel: Term → T → Prop where
| Z: TRel .Zero .N
| S: TRel t .N → TRel (.Succ t) .N
| P: TRel t .N → TRel (.Pred t) .N

/-
theorem countNodes_pos: ∀ (t:Term), countNodes t > 0 := by
  intros t;
  induction t with
  | Zero => simp[countNodes]
  | Succ t' t_ih => simp[countNodes, Nat.add_comm]
  | Pred t t_ih => simp[countNodes, Nat.add_comm]
-/
end Nat

--
--  STLC
--
namespace STLC

inductive T: Type
| Fn (τ₁ τ₂: T)

abbrev Var := String

abbrev Context := Var → T
def augment (Γ: Context) (x: Var) (τ: T): Context := λv ↦ if v=x then τ else Γ v

inductive Term where
| V   (x: Var)
| Abs (x: Var) (τ: T) (b: Term)
| App (t₁ t₂: Term)

def countNodes: Term → Nat
| .V _       => 2
| .Abs _ _ b => 3 + countNodes b
| .App t₁ t₂ => 1 + countNodes t₁ + countNodes t₂

inductive Val: Term → Prop
| A (x: Var) (τ: T) (b: Term): Val (.Abs x τ t)

inductive TRel: Context → Term → T → Prop where
| V (x: Var) (τ: T): Γ x = τ → TRel Γ (.V x) τ
| Abs (x: Var) (b: Term) (τ₁ τ₂: T):
    TRel (augment Γ x τ₁) b τ₂ → TRel Γ (.Abs x τ₁ b) (.Fn τ₁ τ₂)
| App (t₁ t₂: Term) (τ₁ τ₂: T):
    TRel Γ t₁ (.Fn τ₁ τ₂) → TRel Γ t₂ τ₁ → TRel Γ (.App t₁ t₂) τ₂

theorem countNodes_pos: ∀ (t:Term), countNodes t > 0 := by
  intros t;
  induction t with
  | V x => simp[countNodes]
  | Abs x τ b b_ih => simp[countNodes]; rw[Nat.add_comm]; simp
  | App t₁ t₂ t₁_ih t₂_ih => simp[countNodes, Nat.add_assoc, Nat.add_comm 1 _]; simp[←Nat.add_assoc]

end STLC

#print STLC.T
inductive T := Boolean.T |+ Nat.T |+ STLC.T
#print T

inductive Term := Boolean.Term |+ Nat.Term |+ STLC.Term
| isZero (t: Term)
#print Term

fn countNodes := Boolean.countNodes |+ Nat.countNodes |+ STLC.countNodes
| isZero t => 1 + countNodes t
#print countNodes

def countNodes : Term → Nat := λ x ↦
  match x with
  | Term.True => 1
  | Term.False => 1
  | If c t₁ t₂ => 1 + countNodes c + countNodes t₁ + countNodes t₂
  | Term.Zero => 1
  | t.Succ => 1 + countNodes t
  | t.Pred => 1 + countNodes t
  | Term.V x => 2
  | Term.Abs x τ b => 3 + countNodes b
  | t₁.App t₂ => 1 + countNodes t₁ + countNodes t₂
  | isZero t => 1 + countNodes t

def countNodes : Term → Nat := λ x ↦
  let b (x: Boolean.Term) :=
    match x with
    | Boolean.Term.True => 1
    | Boolean.Term.False => 1
    | Boolean.Term.If c t₁ t₂ => 1 + countNodes c + countNodes t₁ + countNodes t₂
  match x with
  | Term.True => b Boolean.Term.True
  | Term.False => b Boolean.Term.False
  | Term.If c t₁ t₂ => b (Boolean.Term.If c t₁ t₂)
  | Term.Zero => 1
  | Term.Succ t => 1 + countNodes t
  | Term.Pred t => 1 + countNodes t
  | Term.V x => 2
  | Term.Abs x τ b => 3 + countNodes b
  | Term.App t₁ t₂ => 1 + countNodes t₁ + countNodes t₂
  | Term.isZero t => 1 + countNodes t

/-
def Boolean.countNodes.inner := fun x: Boolean.Term =>
  Boolean.Term.brecOn x fun x f =>
    (match (motive := (x : Boolean.Term) → Boolean.Term.below x → ℕ) x with
      | Boolean.Term.True => fun x => 1
      | Boolean.Term.False => fun x => 1
      | c.If t₁ t₂ => fun x => 1 + x.1.1 + x.2.1.1 + x.2.2.1)
      f

#print Acc.rec
#print Boolean.Term.rec
#print Boolean.Term.below
#print Boolean.Term.brecOn
#print Boolean.countNodes

#print Boolean.countNodes

#eval countNodes Term.Zero

inductive Val := Boolean.Val |+ Nat.Val |+ STLC.Val
#print Val
#check STLC.augment
def Context := STLC.Var → T

instance: AR.Tools.Compose.Common.SubType STLC.Context Context where
  coe f := λ x ↦ f x

fn augment := STLC.augment
#check STLC.augment
#print STLC.augment
#check augment
#print augment

inductive TRel: Context → Term → T → Prop := Boolean.TRel |+ Nat.TRel |+ STLC.TRel
| iz: TRel Γ t T.N → TRel Γ (.isZero t) T.Bool
#print hidden.TRel
#print TRel
#print STLC.Context
#print CoeDep

/-
theorem countNodes_pos: ∀ (t:Term), countNodes t > 0 := by
  intros t;
  induction t with
  |
-/
-/
