import LeanToolkit

namespace test.nestedTypes

inductive Rose
| node : Nat → List Rose → Rose

inductive Dummy
| d

inductive S := Rose |+ Dummy

/--
info: inductive test.nestedTypes.S : Type
number of parameters: 0
constructors:
test.nestedTypes.S.node : Nat → List S → S
test.nestedTypes.S.d : S
-/
#guard_msgs in
#print S

end test.nestedTypes
