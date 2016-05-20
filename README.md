Richard A. Eisenberg's Dissertation
===================================

This repo stores all the files for my dissertation. I have decided to put
this work-in-progress in the public domain both to generate interest and
to get feedback. Thus, feedback is assuredly welcome, and feel free to post
Issues.

To build, make sure you have all dependencies (see below), but then just use `make`.
If you wish to avoid building my branch of GHC, you can use `make thesis`, which
avoids compiling the examples from the text. You'll still need all the other
dependencies (except Perl) though.

Dependencies:

* A working GHC 8.0.

* Make sure that `ghc-8` is in your path and points to the GHC 8.0 executable.

* Make sure that the packages in the `cab` directory of this repo are installed in
the package database used by `ghc-8`.

* [`ott`](http://www.cl.cam.ac.uk/~pes20/ott/), version 0.23 or greater

* [`latexmk`](http://users.phys.psu.edu/~collins/software/latexmk-jcc/), which
comes with modern LaTeX distributions.

* [`lhs2TeX`](http://www.andres-loeh.de/lhs2tex/), which you can get with
`cabal install lhs2TeX`. (This is just an executable that you need. It does *not*
need to be built with my branch!)

* [Perl](https://www.perl.org/). The use of Perl is very minor and any version from
the last 15 years should work fine.

* [GNU Make](http://www.gnu.org/software/make/). No attempt is made to make the
`Makefile` portable.

* This repo has submodules. Make sure to `git submodule update --init`.
