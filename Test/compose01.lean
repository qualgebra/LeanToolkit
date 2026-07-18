import LeanToolkit

inductive T1
| C1
| C2

inductive T2 where
| C3

inductive sum := T1 |+ T2

/--
info: inductive sum : Type
number of parameters: 0
constructors:
sum.C1 : sum
sum.C2 : sum
sum.C3 : sum
-/
#guard_msgs in
#print sum
