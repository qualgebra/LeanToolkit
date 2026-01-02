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

end Boolean
