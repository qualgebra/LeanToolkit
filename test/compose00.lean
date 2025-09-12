import AR.Tools.Compose

/-
  Testing
-/

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
#print T7

inductive sum1 := T1 |+ T2 |+ T2 |+ T1
| EC

#print sum1
#print SubType.T1.sum1
#print SubType.T2.sum1

def x: T1 := T1.C1

def y: sum1 := x      -- invalid assignment without an up-cast
def z: T1 := sum1.C1  -- invalid assignment without a down-cast

inductive sum2 := T2 |+ T3
#print sum2
#print SubType.T2.sum2
#print SubType.T3.sum2

#print T4
inductive sum3 := T4 |+ T4
#print sum3
#print SubType.T4.sum3


#print T5
inductive sum4 := T5 |+ T5
#print sum4


#print T6
inductive sum5:= T6 |+ T7 |+ T6
#print sum5
#print SubType.T6.sum5
#print SubType.T7.sum5

-- inductive type indices
inductive Boo0 : Nat -> Type
| boo0: Boo0 0
| boo1 (n: Nat): Boo0 (n+1)

inductive Boo1: Nat → Type
| boo (n:Nat): Boo1 n
--| boo' : Boo1 0

#print Boo1
inductive BooSum: Nat → Type := Boo0 |+ Boo1
#print BooSum
#print SubType.Boo0.BooSum
#print SubType.Boo1.BooSum

instance SubType.Boo1.BooSum' (a: ℕ) : SubType (Boo1 a) (BooSum a) where
  coe
    x :=
    match x with
    | Boo1.boo a => BooSum.boo

-- nested data types
inductive Rose where
| node : Nat -> List Rose -> Rose

inductive RoseSum := Rose

instance ins : SubType Rose RoseSum where
  coe
    x :=
    match x with
    | Rose.node a b => RoseSum.node (a) (PolySubType.coe b)

-- dependent types
inductive Foo where
| foo : (n : Nat) -> (v : Vector Nat n) -> Foo

inductive FooSum := Foo

#print FooSum
