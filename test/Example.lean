import LeanToolkit.TAlgebra

namespace Boolean

inductive T where
| Bool

inductive Term where
| True
| False
| If (c t₁ t₂: Term)

inductive Val: Term → Prop
| TT: Val .True
| FF: Val .False

inductive TRel: Term → T → Prop
| TT: TRel .True .Bool
| FF: TRel .False .Bool
| If: TRel c .Bool → TRel t₁ τ → TRel t₂ τ → TRel (.If c t₁ t₂) τ

theorem UniqueType (t: Term): TRel t τ₁ → TRel t τ₂ → τ₁ = τ₂ :=
by
  intros h₁ h₂
  induction h₁ with
  | TT => cases h₂; simp
  | FF => cases h₂; simp
  | If h₃ h₄ h₅ ih₁ ih₂ ih₃ => cases h₂; apply ih₂; assumption;

end Boolean

namespace Nat

inductive T where
| N

inductive Term where
| Zero
| Succ (t: Term)
| Pred (t: Term)

inductive Val: Term → Prop
| Z: Val .Zero
| S: Val v → Val (.Succ v)

inductive TRel: Term → T → Prop where
| Z: TRel .Zero .N
| S: TRel t .N → TRel (.Succ t) .N
| P: TRel t .N → TRel (.Pred t) .N

theorem UniqueType (t: Term): TRel t τ₁ → TRel t τ₂ → τ₁ = τ₂ :=
by
  intros h₁ h₂
  induction h₁ with
  | Z => cases h₂; simp
  | S h₃ ih => apply ih; cases h₂; assumption
  | P h₃ ih => apply ih; cases h₂; assumption

end Nat

inductive T := Boolean.T + Nat.T
#print T

inductive Term := Boolean.Term + Nat.Term
| isZero (t: Term)
#print Term

inductive Val := Boolean.Val + Nat.Val
#print Val

inductive TRel: Term → T → Prop := Boolean.TRel + Nat.TRel
| iz: TRel t T.N → TRel (.isZero t) T.Bool

#print TRel

#print CoeDep
instance: CoeDep Term Term.True Boolean.Term where
  coe := Boolean.Term.True

/-
theorem UniqueType (t: Term): TRel t τ₁ → TRel t τ₂ → τ₁ = τ₂ :=
by
  intros h₁ h₂
  induction h₁ with
  | TT => apply Boolean.UniqueType t
  | FF => apply Boolean.UniqueType
-/
--end BN
