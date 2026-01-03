/-
  negative test cases
-/
import LeanToolkit

/--
error: b is not an inductive type
-/
#guard_msgs in
inductive S := Nat |+ b
