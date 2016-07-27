Haskell translation of Idris's Algebraic Effects Library
--------------------------------------------------------

This directory contains a translation of the algebraic effects
library originally written in Idris for Brady's ICFP 2013 paper,
"Programming and Reasoning with Algebraic Effects and Dependent Types".
It compiles with a version of GHC 8 that has GHC bug [#12442][] fixed.
As of this writing, the fix was not yet merged into the HEAD branch;
it is available on my fork of GHC, on [GitHub][], on the `wip/12442`
branch.

[#12442]: https://ghc.haskell.org/trac/ghc/ticket/12442
[GitHub]: https://github.com/goldfirere/ghc

Files beginning with `Sec` in this directory correspond to sections
in Brady's original paper.

This implementation of algebraic effects is based on the version
described in the paper and available [here][]. Note that this version
is several years old. Newer versions of this library use higher-rank
types in a way not yet available in GHC, though the use case is
encompassed by my design for Dependent Haskell.

[here]: https://github.com/idris-lang/Idris-dev/tree/v0.9.10/libs/effects
