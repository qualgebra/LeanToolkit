import LeanToolkit

namespace test.compose0

inductive T1
| C1
| C2

inductive T2 where
| C3

inductive T3 where
| C1 (n: Nat)
| C2

inductive T4: Nat → Type
| C4{n: Nat}: T4 n
| C5{n: Nat}: T4 n

inductive T5 (y: Nat) where
| C4 (n: Nat)
| C5

inductive T6 (z: Nat) (w: Fin z) where
| C4

inductive T7 (x: Nat) (y: Fin x) where
| C5 (n: Fin x)

inductive sum1 := T1 |+ T2 |+ T2 |+ T1
| EC

/--
info: inductive test.compose0.sum1 : Type
number of parameters: 0
constructors:
test.compose0.sum1.C1 : sum1
test.compose0.sum1.C2 : sum1
test.compose0.sum1.C3 : sum1
test.compose0.sum1.EC : sum1
-/
#guard_msgs in
#print sum1

--#print SubType.T1.sum1
--#print SubType.T2.sum1

--def x: T1 := T1.C1

--def y: sum1 := x      -- invalid assignment without an up-cast
--def z: T1 := sum1.C1  -- invalid assignment without a down-cast

inductive sum2 := T2 |+ T3

/--
info: inductive test.compose0.sum2 : Type
number of parameters: 0
constructors:
test.compose0.sum2.C3 : sum2
test.compose0.sum2.C1 : Nat → sum2
test.compose0.sum2.C2 : sum2
-/
#guard_msgs in
#print sum2

--#print SubType.T2.sum2
--#print SubType.T3.sum2

inductive sum3 := T4 |+ T4

/--
info: inductive test.compose0.sum3 : Nat → Type
number of parameters: 1
constructors:
test.compose0.sum3.C4 : {n : Nat} → sum3 n
test.compose0.sum3.C5 : {n : Nat} → sum3 n
-/
#guard_msgs in
#print sum3

--#print SubType.T4.sum3

inductive sum4 := T5 |+ T5

/--
info: inductive test.compose0.sum4 : Nat → Type
number of parameters: 1
constructors:
test.compose0.sum4.C4 : {y : Nat} → Nat → sum4 y
test.compose0.sum4.C5 : {y : Nat} → sum4 y
-/
#guard_msgs in
#print sum4


inductive sum5:= T6 |+ T7 |+ T6

/--
info: inductive test.compose0.sum5 : (x : Nat) → Fin x → Type
number of parameters: 2
constructors:
test.compose0.sum5.C4 : {z : Nat} → {w : Fin z} → sum5 z w
test.compose0.sum5.C5 : {x : Nat} → {y : Fin x} → Fin x → sum5 x y
-/
#guard_msgs in
#print sum5

--#print SubType.T6.sum5
--#print SubType.T7.sum5

end test.compose0
