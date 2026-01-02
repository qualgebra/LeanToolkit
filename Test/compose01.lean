import AR.Tools.Compose

inductive T1
| C1
| C2

inductive T2 where
| C3

inductive sum := T1 |+ T2
#print sum
