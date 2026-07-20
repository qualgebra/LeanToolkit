# LeanToolkit

This is a prototype implementation of an inductive type composition framework in Lean. More information can be found at the "Modular Composition of Inductive Types Using Lean Meta-programming" paper.

## Directory Structure

    LeanToolkit/
    |- LeanToolkit/ ...... The implementation of the type and function composition framework
    |- Test/ ............. Test cases
    |- CaseStudy/ ........ The case study outlined in the paper

## Quick Start

An installation of Lean 4 (including `elan` and `lake`) is required.

To build the project:

`lake build`

And to run the test cases and the case study:

`lake test`

Each of the test cases uses the `#print` command to display the result of the test case, and the `#guard_msgs` command to compare it against the expected result. 