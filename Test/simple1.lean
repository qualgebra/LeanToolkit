import LeanToolkit

namespace Test.simple0

inductive T1
| C1a
| C1b

inductive T2
| C2a

inductive S := T1 |+ T2

/--
info: inductive Test.simple0.S : Type
number of parameters: 0
constructors:
Test.simple0.S.C1a : S
Test.simple0.S.C1b : S
Test.simple0.S.C2a : S
-/
#guard_msgs in
#print S

end Test.simple0
