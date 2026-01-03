import LeanToolkit

namespace test.dependentTypes

inductive Foo
| foo : (n : Nat) → (v : Vector Nat n) → Foo

inductive Dummy
| d

inductive S := Foo |+ Dummy

/--
info: inductive test.dependentTypes.S : Type
number of parameters: 0
constructors:
test.dependentTypes.S.foo : (n : Nat) → Vector Nat n → S
test.dependentTypes.S.d : S
-/
#guard_msgs in
#print S

end test.dependentTypes
