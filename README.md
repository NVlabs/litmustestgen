# Automatic Synthesis of Comprehensive Memory Model Litmus Test Suites

The technique described in the paper and in the included files shows how to automatically generate a comprehensive suite of ``maximally-interesting'' litmus tests specific to a given (axiomatic specification of) memory model.  This enables more rapid and more reliable exploration of sophisticated memory models such as those used by C/C++, IBM Power, and more.

## Installation

None needed!  Just open the `.als` files in [Alloy](http://alloy.mit.edu) and execute them.

## Usage

To use our canonicalizer script:

* a Java compiler `javac`
* `python` (tested on version 2.7)
* Download the Alloy 4.2 [.jar file](http://alloy.mit.edu/alloy/downloads/alloy4.2.jar)
* run `make` to build our ever-so-slightly-customized command-line interface to Alloy.  (All that is changed is the particular set of command line flags, and generation is run until exhaustion.)

Basic usage:

    ./run.sh <.als input file> -m <test size bound> <test name>

For example:

    $ ./run.sh tso_perturbed.als -m 4 causality
    # ['canon.py', '20170331-164702-causality-4']
      Command match: causality
    Scope bound 4 overrides default bound of 4
    New hash (1/1): _T_Wa0_Wa0
    New hash (2/2): _T_Ra0_Wa1_T_Wa1_Wa0
    New hash (3/3): _T_Wa0_Wa1_T_Wa1_Wa0
    New hash (4/4): _T_Ra0_Ra0_T_Wa0_T_Wa0
    New hash (5/5): _T_Ra0_Ra0_T_Wa0_Wa0
    New hash (6/7): _T_Ra0_Ra0_T_Wa0
    New hash (7/9): _T_Wa0_T_Wa0_Ra0_Ra0
    New hash (8/10): _T_Ra0_Ra1_T_Wa1_Wa0
    New hash (9/11): _T_Ra0_Wa1_T_Ra1_Wa0
    New hash (10/12): _T_Ra0_Wa0_T_Wa0
    #,Filename,Command,Unique,Total
    Results,tso_perturbed.als,causality,10,12

    real    0m1.123s
    user    0m2.246s
    sys     0m0.073s

This lists the ten tests that are minimal with respect to the TSO causality axiom, in no particular order:

1. CoWW
2. S
3. 2+2W
4. W+W+RR
5. CoMP
6. CoRR
7. W+WRR
8. MP
9. LB
10. CoRW

This matches the set of ten described in the paper.  In this case, Alloy generated 12 hashes, of which 10 were unique post-canonicalization.

The hashes themselves are a bit obscure but should be human-readable:

Hash item | Meaning
----------|--------
T | start of thread
R | Read
W | Write
Aq | Acquire
Rl | Release
AA | Atomic read-modify-write
F | Fence
a*n* | Address *n*
m | Read half of a read-modify-write
s*n* | Source of dependency *n*
ra*n* | Target of address dependency *n*
rc*n* | Target of control dependency *n*
rd*n* | Target of data dependency *n*
na | non-atomic
rx | memory_order_relaxed
aq | memory_order_acquire
rl | memory_order_release
ar | memory_order_acq_rel
sc | memory_order_seq_cst

## Experimenting with the Technique

Feel free to play around with this and let us know what you think!  If you find anything interesting, let us know!

For example, consider this simple experiment:

If `fr_p` is defined as follows:

    fun fr_p[p: PTag->univ] : Read->Write { (Read - p[RE]) <: fr :> (Write - p[RE]) }

The seven tests above are emitted.  If instead, `fr_p` is redefined as follow:

    fun fr_p[p: PTag->univ] : Read->Write {
      ( ~(rf_p[p]).^(co_p[p]) )
      +
      ( (Read-(Write.rf)-p[RE]) <: address.~address :> (Write - p[RE]) )
    }

Then `fr_p` is more tightly constrained, and W+W+RR, W+WRR, and CoMP are no longer emitted.

## Extending the Infrastructure

The canonicalizer is still somewhat primitive and has at least one known scenario where it misses some duplicates.  It should be easy to extend/replace the script and/or our command line interface to Alloy to suit your own needs.

## Questions?

Please contact Dan Lustig at dlustig@nvidia.com

## Attribution

If you use these techniques in your work, please cite our ASPLOS 2017 paper:

Daniel Lustig, Andy Wright, Alexandros Papakonstantinou, and Olivier Giroux,
 "Automatic Synthesis of Comprehensive Memory Model Litmus Test Suites",
22nd ACM International Conference on Architectural Support for Programming Languages and Operating Systems (ASPLOS), Xi'an, China, April 8-12, 2017

([Paper](fixme)) ([Slides](coming_soon)) coming soon!
