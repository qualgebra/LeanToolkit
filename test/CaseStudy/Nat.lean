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

end Nat
