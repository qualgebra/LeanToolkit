import LeanToolkit

namespace test.rec0

inductive T1
| T1.C1
| T1.C2 (x:T1)

inductive T2
| T2.C3

inductive S := T1 |+ T2

/--
info: inductive test.rec0.S : Type
number of parameters: 0
constructors:
test.rec0.S.C1 : S
test.rec0.S.C2 : S → S
test.rec0.S.C3 : S
-/
#guard_msgs in
#print S

end test.rec0
