import LeanToolkit

/- TODO -/
/-
namespace test.nestedTypes

inductive Rose
| node : Nat → List Rose → Rose

inductive Dummy
| d

inductive S := Rose |+ Dummy

inductive S
| node : Nat → List S → S
| d

--#print SubType.test.nestedTypes.Rose.S

--#print test.nestedTypes.Rose.S.coe
instance inst: Coe test.nestedTypes.Rose S where
  coe (x: test.nestedTypes.Rose): S :=
--def test.nestedTypes.Rose.S.coe' (x : test.nestedTypes.Rose) : S :=
  match x with
  | test.nestedTypes.Rose.node a b => S.node a (inst.coe <$> b) --(test.nestedTypes.Rose.S.coe' <$> b)

#print inst
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
-/
