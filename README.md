# Software Foundations

This repository contains the examples and exercises
I completed while reading the [Software Foundation](https://softwarefoundations.cis.upenn.edu/) series.

## Logical Foundations

  * ### Functional Programming in Coq
    - `Basics.v`
  * ### Proof by Induction
    - `Induction.v`

# Building the project
To generate the Makefile, used to build the project, run the following from
each subdirectory.

    coq_makefile -f _CoqProject *.v -o Makefile
