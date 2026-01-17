import LeanToolkit

inductive T1
| C1a
| C1b

inductive T2
| C2a

inductive S := T1 |+ T2

/--
info: inductive S : Type
number of parameters: 0
constructors:
S.C1a : S
S.C1b : S
S.C2a : S
-/
#guard_msgs in
#print S

/--
info: def CoeDep.S.C1a.T1 : CoeDep S S.C1a T1 :=
{ coe := T1.C1a }
-/
#guard_msgs in
#print CoeDep.S.C1a.T1

/--
info: def CoeDep.S.C1b.T1 : CoeDep S S.C1b T1 :=
{ coe := T1.C1b }
-/
#guard_msgs in
#print CoeDep.S.C1b.T1

/--
info: def T1.S.coe : T1 → S :=
fun x =>
  match x with
  | T1.C1a => S.C1a
  | T1.C1b => S.C1b
-/
#guard_msgs in
#print T1.S.coe

/--
info: def SubType.T1.S : SubType T1 S :=
{ coe := T1.S.coe }
-/
#guard_msgs in
#print SubType.T1.S

/--
info: def CoeDep.S.C2a.T2 : CoeDep S S.C2a T2 :=
{ coe := T2.C2a }
-/
#guard_msgs in
#print CoeDep.S.C2a.T2

/--
info: def T2.S.coe : T2 → S :=
fun x =>
  match x with
  | T2.C2a => S.C2a
-/
#guard_msgs in
#print T2.S.coe

/--
info: def SubType.T2.S : SubType T2 S :=
{ coe := T2.S.coe }
-/
#guard_msgs in
#print SubType.T2.S

def x: S := T1.C1a -- up-cast
def y: T1 := S.C1a -- down-cast
