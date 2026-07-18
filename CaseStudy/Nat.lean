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

@[simp] def countNodes: Term → Nat
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

theorem notEmpty(t: Term): countNodes t > 0 := by
  induction t with
  | Zero => simp
  | Succ t' ih => simp[Nat.succ_add]
  | Pred t' ih => simp[Nat.succ_add]

end Nat
