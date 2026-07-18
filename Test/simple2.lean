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
info: def coeDep.S.C1a.T1 : CoeDep S S.C1a T1 :=
{ coe := T1.C1a }
-/
#guard_msgs in
#print coeDep.S.C1a.T1

/--
info: def coeDep.S.C1b.T1 : CoeDep S S.C1b T1 :=
{ coe := T1.C1b }
-/
#guard_msgs in
#print coeDep.S.C1b.T1

/--
info: def coeDep.S.C2a.T2 : CoeDep S S.C2a T2 :=
{ coe := T2.C2a }
-/
#guard_msgs in
#print coeDep.S.C2a.T2

def index1: T1 → Nat
| .C1a => 1
| .C1b => 2

def index2: T2 → Nat
| .C2a => 1

fn indexS: S → Nat := index1 |+ index2

/--
info:
def indexS : S → Nat :=
fun x =>
  match x with
  | S.C1a => index1 T1.C1a
  | S.C1b => index1 T1.C1b
  | S.C2a => index2 T2.C2a
-/
#guard_msgs in
#print indexS
