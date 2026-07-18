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

@[simp] def countNodes: Term → Nat
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

theorem notEmpty(t: Term): countNodes t > 0 := by
  induction t with
  | V => simp
  | Abs x τ b ih => apply Nat.lt_add_left; apply ih
  | App t₁ t₂ ih₁ ih₂ => simp[Nat.succ_add]

end STLC
