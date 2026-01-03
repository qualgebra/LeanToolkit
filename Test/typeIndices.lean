import LeanToolkit

namespace test.typeIndices

inductive T1: Nat → Type
| C1 : T1 0

inductive T2: Nat → Type
| C2: T2 1

inductive S := T1 |+ T2

/--
info: inductive test.typeIndices.S : Nat → Type
number of parameters: 0
constructors:
test.typeIndices.S.C1 : S 0
test.typeIndices.S.C2 : S 1
-/
#guard_msgs in
#print S

end test.typeIndices
