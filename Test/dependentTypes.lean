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

/--
info: def test.dependentTypes.coeDep.S.foo.test.dependentTypes.Foo : {n : Nat} →
  {v : Vector Nat n} → CoeDep S (S.foo n v) Foo :=
fun {n} {v} => { coe := Foo.foo n v }
-/
#guard_msgs in
#print coeDep.S.foo.test.dependentTypes.Foo

/--
info: def test.dependentTypes.coe.test.dependentTypes.Foo.S : Foo → S :=
fun x =>
  match x with
  | Foo.foo n v => S.foo n v
-/
#guard_msgs in
#print coe.test.dependentTypes.Foo.S

/--
info: def test.dependentTypes.SubType.test.dependentTypes.Foo.S : SubType Foo S :=
{ coe := coe.test.dependentTypes.Foo.S } -/
#guard_msgs in
#print SubType.test.dependentTypes.Foo.S

/--
info: def test.dependentTypes.coeDep.S.d.test.dependentTypes.Dummy : CoeDep S S.d Dummy :=
{ coe := Dummy.d }
-/
#guard_msgs in
#print coeDep.S.d.test.dependentTypes.Dummy

/--
info: def test.dependentTypes.coe.test.dependentTypes.Dummy.S : Dummy → S :=
fun x =>
  match x with
  | Dummy.d => S.d
-/
#guard_msgs in
#print coe.test.dependentTypes.Dummy.S

/--
info: def test.dependentTypes.SubType.test.dependentTypes.Dummy.S : SubType Dummy S :=
{ coe := coe.test.dependentTypes.Dummy.S }
-/
#guard_msgs in
#print SubType.test.dependentTypes.Dummy.S

def v: Vector Nat 1 := Vector.mk #[7] (by simp)
def x: Foo := Foo.foo 1 v
def y: S := x
def z: Foo := S.foo 1 v

end test.dependentTypes
