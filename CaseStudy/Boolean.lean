--
-- Boolean
--
namespace Boolean

inductive T where
| Bool

inductive Term where
| True | False
| If (c t₁ t₂: Term)

@[simp]
def countNodes: Term → Nat
| .True => 1
| .False => 1
| .If c t₁ t₂ => 1 + countNodes c + countNodes t₁ + countNodes t₂

inductive Val: Term → Prop
| T: Val .True | F: Val .False

theorem notEmpty(t: Term): countNodes t > 0 := by
  induction t with
  | True => simp
  | False => simp
  | If c t₁ t₂ c_ih t₁_ih t₂_ih => simp[Nat.succ_add]

inductive TRel: Term → T → Prop
| TT: TRel .True .Bool
| FF: TRel .False .Bool
| If: TRel c .Bool → TRel t₁ τ → TRel t₂ τ → TRel (.If c t₁ t₂) τ

end Boolean
