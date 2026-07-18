import LeanToolkit
import Lean.Meta.Tactic

open Lean Meta Elab.Tactic Meta.Tactic
open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std


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
info: def coe.T1.S : T1 → S :=
fun x =>
  match x with
  | T1.C1a => S.C1a
  | T1.C1b => S.C1b
-/
#guard_msgs in
#print coe.T1.S

/--
info: def SubType.T1.S : SubType T1 S :=
{ coe := coe.T1.S }
-/
#guard_msgs in
#print SubType.T1.S

/--
info: def coeDep.S.C2a.T2 : CoeDep S S.C2a T2 :=
{ coe := T2.C2a }
-/
#guard_msgs in
#print coeDep.S.C2a.T2

/--
info: def coe.T2.S : T2 → S :=
fun x =>
  match x with
  | T2.C2a => S.C2a
-/
#guard_msgs in
#print coe.T2.S

/--
info: def SubType.T2.S : SubType T2 S :=
{ coe := coe.T2.S }
-/
#guard_msgs in
#print SubType.T2.S

def x: S := T1.C1a -- up-cast
def y: T1 := S.C1a -- down-cast

/-
  function summation testing
-/
def f1: T1 → Char
| T1.C1a => 'a'
| T1.C1b => 'b'

def f2: T2 → Char
| T2.C2a => 'a'

fn fSum: S → Char := f1 |+ f2

/--
info: def fSum : S → Char :=
fun x =>
  match x with
  | S.C1a => f1 T1.C1a
  | S.C1b => f1 T1.C1b
  | S.C2a => f2 T2.C2a
-/
#guard_msgs in
#print fSum
