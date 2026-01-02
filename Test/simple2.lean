import LeanToolkit

inductive T1
| C1a
| C1b

--def index1: T1 → Nat
--| T1.C1a => 0
--| T1.C1b => 1

inductive T2
| C2a

--def index2: T2 → Nat
--| T2.C2a => 2

inductive S := T1 |+ T2

/--
info: inductive S : Type
number of parameters: 0
constructors:
S.C1a : S
S.C1b : S
S.C2a : S
-/
#guard_msgs in
#print S

--instance: CoeDep S S.C1a T1 where
--  coe := T1.C1a

--instance: CoeDep S S.C1b T1 where
--  coe := T1.C1b

--instance: CoeDep S S.C2a T2 where
--  coe := T2.C2a

-- def index: S → Nat
-- | S.C1a => index1 S.C1a
-- | S.C1b => index1 S.C1b
-- | S.C2a => index2 S.C2a

-- def index'(x:S): Nat := by
--   cases x with
--   | C1a => apply index1 S.C1a
--   | C1b => apply index1 S.C1b
--   | C2a => apply index2 S.C2a

-- fn index'' := index1 |+ index2
-- #print index''
