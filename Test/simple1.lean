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

/--
info: def Test.simple0.CoeDep.S.C1a.Test.simple0.T1 : CoeDep S S.C1a T1 :=
{ coe := T1.C1a }
-/
#guard_msgs in
#print CoeDep.S.C1a.Test.simple0.T1

/--
info: def Test.simple0.CoeDep.S.C1b.Test.simple0.T1 : CoeDep S S.C1b T1 :=
{ coe := T1.C1b }
-/
#guard_msgs in
#print CoeDep.S.C1b.Test.simple0.T1


/--
info: def Test.simple0.coe.Test.simple0.T1.S : T1 → S :=
fun x =>
  match x with
  | T1.C1a => S.C1a
  | T1.C1b => S.C1b
-/
#guard_msgs in
#print coe.Test.simple0.T1.S

/--
info: def Test.simple0.SubType.Test.simple0.T1.S : SubType T1 S :=
{ coe := coe.Test.simple0.T1.S }
-/
#guard_msgs in
#print SubType.Test.simple0.T1.S

/--
info: def Test.simple0.CoeDep.S.C2a.Test.simple0.T2 : CoeDep S S.C2a T2 :=
{ coe := T2.C2a }
-/
#guard_msgs in
#print CoeDep.S.C2a.Test.simple0.T2

/--
info: def Test.simple0.coe.Test.simple0.T2.S : T2 → S :=
fun x =>
  match x with
  | T2.C2a => S.C2a
-/
#guard_msgs in
#print coe.Test.simple0.T2.S

/--
info: def Test.simple0.SubType.Test.simple0.T2.S : SubType T2 S :=
{ coe := coe.Test.simple0.T2.S }
-/
#guard_msgs in
#print SubType.Test.simple0.T2.S

def x: S := T1.C1a -- up-cast
def y: T1 := S.C1a -- down-cast

end Test.simple0
