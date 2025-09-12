import CaseStudy.Boolean
import CaseStudy.Nat
import CaseStudy.STLC
import LeanToolkit

set_option pp.fieldNotation false

inductive T := Boolean.T |+ Nat.T |+ STLC.T
#print T

inductive Term := Boolean.Term |+ Nat.Term |+ STLC.Term
| isZero (t: Term)
#print Term
#print hidden.Term

fn countNodes := Boolean.countNodes |+ Nat.countNodes |+ STLC.countNodes
| Term.isZero t => 1 + countNodes t
#print countNodes

inductive Val := Boolean.Val |+ Nat.Val |+ STLC.Val
#print Val
#check STLC.augment
def Context := STLC.Var → T

instance: SubType STLC.Context Context where
  coe f := λ x ↦ f x

fn augment := STLC.augment
#check STLC.augment
#print STLC.augment
#check augment
#print augment


inductive TRel: Context → Term → T → Prop := Boolean.TRel |+ Nat.TRel |+ STLC.TRel
| iz: TRel Γ t T.N → TRel Γ (Term.isZero t) T.Bool

#print hidden.TRel
#print TRel
#print STLC.Context
#print CoeDep
#print hidden.Term
