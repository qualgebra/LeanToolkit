import LeanToolkit

/- TODO: The CoeDep instances depend on type indices, and this doesn't seem to work currently. -/
/-
namespace test.typeIndices

inductive T1: Nat → Type
| C1 : T1 0
| C2 (x: T1 n) : T1 (n+1)

inductive T2: Nat → Type
| C3: T2 1

inductive S := T1 |+ T2

abbrev X := T1

instance CoeDep.S.C1.test.typeIndices.T1l: CoeDep (S _) (S.C1) (X 0) where
  coe := T1.C1 --test.typeIndices.T1.C1

/--
info: inductive test.typeIndices.S : Nat → Type
number of parameters: 0
constructors:
test.typeIndices.S.C1 : S 0
test.typeIndices.S.C2 : {n : Nat} → S n → S (n + 1)
test.typeIndices.S.C3 : S 1
-/
#guard_msgs in
#print S

/--
info: def test.typeIndices.test.typeIndices.T1.S.coe : {a : Nat} → T1 a → S a :=
fun {a} x =>
  T1.brecOn x fun {a} x f =>
    (match (motive := (a : Nat) → (x : T1 a) → T1.below x → S a) a, x with
      | .(0), T1.C1 => fun x => S.C1
      | .(n + 1), x.C2 => fun x => S.C2 x.1)
      f
-/
#guard_msgs in
#print test.typeIndices.T1.S.coe

/--
info: def test.typeIndices.SubType.test.typeIndices.T1.S : {a : Nat} → SubType (T1 a) (S a) :=
fun {a} => { coe := test.typeIndices.T1.S.coe }
-/
#guard_msgs in
#print SubType.test.typeIndices.T1.S

def x := T1.C1
def y: S 0 := x

def a := T1.C2 x
def b: S 1 := a

/--
info: def test.typeIndices.test.typeIndices.T2.S.coe : {a : Nat} → T2 a → S a :=
fun {a} x =>
  match a, x with
  | .(1), T2.C3 => S.C3
-/
#guard_msgs in
#print test.typeIndices.T2.S.coe

/--
info: def test.typeIndices.SubType.test.typeIndices.T2.S : {a : Nat} → SubType (T2 a) (S a) :=
fun {a} => { coe := test.typeIndices.T2.S.coe }
-/
#guard_msgs in
#print SubType.test.typeIndices.T2.S

end test.typeIndices
-/
