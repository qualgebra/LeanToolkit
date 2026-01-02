import LeanToolkit

inductive T1
| C1a
| C1b

inductive T2
| C2a

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
