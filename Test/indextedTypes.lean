import LeanToolkit

inductive X: Nat → Type
| x: X 0

inductive Y: Nat → Type
| y: Y 1

inductive Z := X |+ Y

/--
info:
inductive Z : Nat → Type
number of parameters: 0
constructors:
Z.x : Z 0
Z.y : Z 1
-/
#guard_msgs in
#print Z
