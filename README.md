## About

This is the code repository for a toy compiler that is proven fully abstract (preserves and reflects equivalences). It has a compiler
for arithmetic expressions to a tiny stack machine (idea came from Adam
Chlipala's [CPDT]((http://adam.chlipala.net/cpdt/))).

The proofs follow a style that is essentially a modified version of the proof
style advocated by Adam Chlipala in [Certified Programming with Dependent
Types](http://adam.chlipala.net/cpdt/) -- modified slightly in that hints are
always kept extremely locally scoped. The intention behind this (explained a
little further in the library repository for the couple tactics that implement
this: [dbp/literatecoq](https://github.com/dbp/literatecoq)) is to make
reading proofs be as easy as possible, where on paper you would write "follows
by induction using X, Y, and Z". When hints end up in global databases, you can
end up writing proofs that say "follows by induction using X, Z", because you
had hinted Y somewhere earlier.

## Writeup

The accompanying writeup for this compiler is at [https://dbp.io/essays/2018-04-19-how-to-prove-a-compiler-fully-abstract.html](https://dbp.io/essays/2018-04-19-how-to-prove-a-compiler-fully-abstract.html).

## Setup

This requires [opam](https://opam.ocaml.org/), in order to install Coq (or
install Coq some other way, but [opam](https://opam.ocaml.org/) is recommended).

Download the submodules that contains the `literatecoq` tactics with:

```
git submodule init
git submodule update
```

Then you need to get Coq (tested with 8.6, 8.7.2, and 8.8.0: earlier/later may
work):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update && opam install coq.8.8.0
```

Once Coq has been installed, you can build the `literatecoq` library:

```
make -C literatecoq
```

## Proving

The proofs are all in `src/Proofs.v`, which you can open up in your favorite
editor for Coq (Proof General & Emacs being common).

Obviously, this tiny example is not going to teach you how to prove things in
Coq! There are various resources how to do that. A good one that used to not be
online but now seems to be is Bertot and Casteron's [Coq'Art: Interactive
Theorem Proving and Program
Development](https://archive.org/details/springer_10.1007-978-3-662-07964-5).
Classics that have always been online are [Certified Programming with Dependent
Types](http://adam.chlipala.net/cpdt/) and [Software
Foundations](https://softwarefoundations.cis.upenn.edu/). Theorem proving (of
which I'm still quite new at) seems to be a skill that relies on three pretty
different skills: deep understanding of typed functional programming concepts,
normal paper-and-pencil proof strategy, and understanding the abilities / quirks
of the particular system you are using. 
