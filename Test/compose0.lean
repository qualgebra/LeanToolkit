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

/--
info: def test.compose0.CoeDep.sum1.C1.test.compose0.T1 : CoeDep sum1 sum1.C1 T1 :=
{ coe := T1.C1 }
-/
#guard_msgs in
#print CoeDep.sum1.C1.test.compose0.T1

/--
info: def test.compose0.CoeDep.sum1.C2.test.compose0.T1 : CoeDep sum1 sum1.C2 T1 :=
{ coe := T1.C2 }
-/
#guard_msgs in
#print CoeDep.sum1.C2.test.compose0.T1

/--
info: def test.compose0.SubType.test.compose0.T1.sum1 : SubType T1 sum1 :=
{ coe := coe.test.compose0.T1.sum1 }
-/
#guard_msgs in
#print SubType.test.compose0.T1.sum1

/--
info: def test.compose0.CoeDep.sum1.C3.test.compose0.T2 : CoeDep sum1 sum1.C3 T2 :=
{ coe := T2.C3 }
-/
#guard_msgs in
#print CoeDep.sum1.C3.test.compose0.T2

/--
info: def test.compose0.coe.test.compose0.T2.sum1 : T2 → sum1 :=
fun x =>
  match x with
  | T2.C3 => sum1.C3
-/
#guard_msgs in
#print coe.test.compose0.T2.sum1

/--
info: def test.compose0.SubType.test.compose0.T2.sum1 : SubType T2 sum1 :=
{ coe := coe.test.compose0.T2.sum1 }
-/
#guard_msgs in
#print SubType.test.compose0.T2.sum1

def x: T1 := T1.C1

def y: sum1 := x      -- invalid assignment without an up-cast
def z: T1 := sum1.C1  -- invalid assignment without a down-cast

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

/--
info: def test.compose0.CoeDep.sum2.C3.test.compose0.T2 : CoeDep sum2 sum2.C3 T2 :=
{ coe := T2.C3 }
-/
#guard_msgs in
#print CoeDep.sum2.C3.test.compose0.T2

/--
info: def test.compose0.coe.test.compose0.T2.sum2 : T2 → sum2 :=
fun x =>
  match x with
  | T2.C3 => sum2.C3
-/
#guard_msgs in
#print coe.test.compose0.T2.sum2

/--
info: def test.compose0.SubType.test.compose0.T2.sum2 : SubType T2 sum2 :=
{ coe := coe.test.compose0.T2.sum2 }
-/
#guard_msgs in
#print SubType.test.compose0.T2.sum2

/--
info: def test.compose0.CoeDep.sum2.C1.test.compose0.T3 : {n : Nat} → CoeDep sum2 (sum2.C1 n) T3 :=
fun {n} => { coe := T3.C1 n }
-/
#guard_msgs in
#print CoeDep.sum2.C1.test.compose0.T3

/--
info: def test.compose0.CoeDep.sum2.C2.test.compose0.T3 : CoeDep sum2 sum2.C2 T3 :=
{ coe := T3.C2 }
-/
#guard_msgs in
#print CoeDep.sum2.C2.test.compose0.T3

/--
info: def test.compose0.coe.test.compose0.T3.sum2 : T3 → sum2 :=
fun x =>
  match x with
  | T3.C1 n => sum2.C1 n
  | T3.C2 => sum2.C2
-/
#guard_msgs in
#print coe.test.compose0.T3.sum2

/--
info: def test.compose0.SubType.test.compose0.T3.sum2 : SubType T3 sum2 :=
{ coe := coe.test.compose0.T3.sum2 }
-/
#guard_msgs in
#print SubType.test.compose0.T3.sum2

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

/--
info: def test.compose0.CoeDep.sum3.C4.test.compose0.T4 : {a : Nat} → CoeDep (sum3 a) sum3.C4 (T4 a) :=
fun {a} => { coe := T4.C4 }
-/
#guard_msgs in
#print CoeDep.sum3.C4.test.compose0.T4

/--
info: def test.compose0.CoeDep.sum3.C5.test.compose0.T4 : {a : Nat} → CoeDep (sum3 a) sum3.C5 (T4 a) :=
fun {a} => { coe := T4.C5 }
-/
#guard_msgs in
#print CoeDep.sum3.C5.test.compose0.T4

/--
info: def test.compose0.coe.test.compose0.T4.sum3 : {a : Nat} → T4 a → sum3 a :=
fun {a} x =>
  match x with
  | T4.C4 => sum3.C4
  | T4.C5 => sum3.C5
-/
#guard_msgs in
#print coe.test.compose0.T4.sum3

/--
info: def test.compose0.SubType.test.compose0.T4.sum3 : {a : Nat} → SubType (T4 a) (sum3 a) :=
fun {a} => { coe := coe.test.compose0.T4.sum3 }
-/
#guard_msgs in
#print SubType.test.compose0.T4.sum3

/-
 TODO: this example combines depend types and type families, and we still don't support families.

inductive sum5:= T6 |+ T7 |+ T6

/-
problem: implicit parameters with the same name as the type parameters
are shadowing them.
-/

#print CoeDep.sum5.C5.test.compose0.T7
/--
info: inductive test.compose0.sum5 : (x : Nat) → Fin x → Type
number of parameters: 2
constructors:
test.compose0.sum5.C4 : {z : Nat} → {w : Fin z} → sum5 z w
test.compose0.sum5.C5 : {x : Nat} → {y : Fin x} → Fin x → sum5 x y
-/
#guard_msgs in
#print sum5

/--
info: def test.compose0.CoeDep.sum5.C4.test.compose0.T6 : {x : Nat} → {y : Fin x} → CoeDep (sum5 x y) sum5.C4 (T6 x y) :=
fun {x} {y} => { coe := T6.C4 }
-/
#guard_msgs in
#print CoeDep.sum5.C4.test.compose0.T6

/--
info: def test.compose0.test.compose0.T6.sum5.coe : {x : Nat} → {y : Fin x} → T6 x y → sum5 x y :=
fun {x} {y} x_1 =>
  match x_1 with
  | T6.C4 => sum5.C4
-/
#guard_msgs in
#print test.compose0.T6.sum5.coe

/--
info: def test.compose0.SubType.test.compose0.T6.sum5 : {x : Nat} → {y : Fin x} → SubType (T6 x y) (sum5 x y) :=
fun {x} {y} => { coe := test.compose0.T6.sum5.coe }
-/
#guard_msgs in
#print SubType.test.compose0.T6.sum5

#print CoeDep.sum5.C5.test.compose0.T7

/--
info: def test.compose0.test.compose0.T7.sum5.coe : {x : Nat} → {y : Fin x} → T7 x y → sum5 x y :=
fun {x} {y} x_1 =>
  match x_1 with
  | T7.C5 n => sum5.C5 n
-/
#guard_msgs in
#print test.compose0.T7.sum5.coe

/--
info: def test.compose0.SubType.test.compose0.T7.sum5 : {x : Nat} → {y : Fin x} → SubType (T7 x y) (sum5 x y) :=
fun {x} {y} => { coe := test.compose0.T7.sum5.coe }
-/
#guard_msgs in
#print SubType.test.compose0.T7.sum5
-/

end test.compose0
