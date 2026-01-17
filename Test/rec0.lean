import LeanToolkit

namespace test.rec0

inductive T1
| C1
| C2 (x:T1)

inductive T2
| C3

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

/--
info: def test.rec0.CoeDep.S.C1.test.rec0.T1 : CoeDep S S.C1 T1 :=
{ coe := T1.C1 }
-/
#guard_msgs in
#print CoeDep.S.C1.test.rec0.T1

/--
info: def test.rec0.test.rec0.T1.S.coe : T1 → S :=
fun x =>
  T1.brecOn x fun x f =>
    (match (motive := (x : T1) → T1.below x → S) x with
      | T1.C1 => fun x => S.C1
      | x.C2 => fun x => S.C2 x.1)
      f
-/
#guard_msgs in
#print test.rec0.T1.S.coe

/--
info: def test.rec0.SubType.test.rec0.T1.S : SubType T1 S :=
{ coe := test.rec0.T1.S.coe }
-/
#guard_msgs in
#print SubType.test.rec0.T1.S

/--
info: def test.rec0.CoeDep.S.C3.test.rec0.T2 : CoeDep S S.C3 T2 :=
{ coe := T2.C3 }
-/
#guard_msgs in
#print CoeDep.S.C3.test.rec0.T2

/--
info: def test.rec0.test.rec0.T2.S.coe : T2 → S :=
fun x =>
  match x with
  | T2.C3 => S.C3
-/
#guard_msgs in
#print test.rec0.T2.S.coe
/--
info: def test.rec0.SubType.test.rec0.T2.S : SubType T2 S :=
{ coe := test.rec0.T2.S.coe }
-/
#guard_msgs in
#print SubType.test.rec0.T2.S

def x: T1 := T1.C1
def y: S := x

def a: T1 := S.C1
def b: T2 := S.C3

end test.rec0
