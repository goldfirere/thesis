%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import Data.Kind ( type (*), Type )
import Data.Nat
import Effects
import Effect.StdIO
import Effect.Exception
import Effect.Random
import Effect.State
import Data.AChar
import Effect.File
import Prelude ( Maybe(..), lookup, (++), (<$>), (<*>), IO
               , not, reverse, ($) )
import Data.Singletons
import Util.If
import Control.Catchable

type Read = !Read

\end{code}

%endif

\def\effects/{\package{Effects}}

\subsection{Algebraic effects}

\citet{algebraic-effects} describes an approach to the challenge of embedding
side effects into a pure, functional language. His approach is to
use composable algebraic effects, implemented as a domain-specific language
embedded in Idris~\cite{idris}, a full spectrum dependently typed language.
This technique is meant to contrast with Haskell's monad transformers~\cite{monad-transformers}.
Brady's
library, \effects/, is translatable directly into Dependent Haskell. With heavy
use of singletons, all of the code described in the original paper
is even implementable in GHC 8.\footnote{The code is
available at \url{https://github.com/goldfirere/thesis/tree/master/effects}.
It does not compile with GHC 8.0.1 due to a small implementation bug.
The fix is in the latest development version of GHC and may be available
in GHC 8.0.2.}

\subsubsection{Example 1: an simple expression interpreter}

To give you an idea of the power and flexibility of the algebraic
effects approach, let's look at a function that interprets a simple
expression language.\footnote{This example is adapted from \citet[Section 2.1.3]{algebraic-effects}.}
Here is the expression AST:
\begin{code}
data Expr = Val Nat | Add Expr Expr | Var String | Random Nat
\end{code}
Expressions can contain literal numbers,\footnote{I have restricted
this and other examples to work with naturals only. This restriction is
in place solely to play nicely with the use of singletons to translate
the Idris library into a form compatible with GHC 8. In a full
Dependent Haskell implementation, this restriction would not be necessary.}
additions, variable references, and naturals randomly generated up to
some specified limit. In the version we will consider, the interpreter
is instrumented to print out the value of every random number generated.
Thus the interpreter needs four different effectful capabilities:
the ability to deal with errors (in case a named variable does not
exist), the ability to write output, access to a pseudo-random number
generator, and an ambient environment of defined variables.
This ambient environment has type |Vars|, an association list mapping
variable names to their values:
\begin{code}
type Vars = [(String, Nat)]
\end{code}
With all that in hand, here is the evaluator:
\begin{working}
\begin{code}
eval  ::  Handler StdIO e
      =>  Expr -> Eff e ![EXCEPTION String, STDIO, RND, STATE Vars] Nat
eval (Val x)         = return x
eval (Var x)         = do  vs <- get
                           case lookup x vs of
                             Nothing   -> raise ("Unknown var: " ++ x)
                             Just val  -> return val
eval (Add l r)       = (+) <$> eval l <*> eval r
eval (Random upper)  = do  num <- rndNat 0 upper
                           putStrLn ("Random value: " ++ show num)
                           return num
\end{code}
\end{working}
Let's first look at the type of |eval|, with our goal being a general
understanding of what this technique brings us, not working out all the
details.

The return type of this function is a specialization of |Eff|,
a type defined by the \effects/ library. |Eff| is not a monad; the use
of |do|-notation in the code in this section is enabled by the GHC
extension \ext{RebindableSyntax}. With \ext{RebindableSyntax}, GHC
uses whatever symbols are in scope to implement various features. In
our case, \effects/ defines |>>| and |>>=| operators which work over
|Eff|.

|Eff| takes three parameters: an underlying effect handler |e|,
a type-level list of capabilities, and the return type of the
computation. The underlying effect handler must be able to handle
read and write commands. We would generally expect this to be |IO|,
but an environment with an input list of strings and an output list
of strings could be used to model I/O in a pure environment.
The list of capabilities is better viewed as a set, as the order
in this list is immaterial. Fancy footwork done by the types of
the operations provided by the capabilities (like |get| or |rndNat|)
looks up the capability in the list, regardless of order.

Once we've absorbed the type of |eval|, its body is rather uninteresting---but
that's exactly the point! We need not |lift| one capability through another
(as must be done with monad transformers) nor give any indication of
how our capabilities are structured. It all just works.

\subsubsection{Automatic lifting}

In the example above, we can use the |STATE| capability with its |get|
accessor, despite the fact that |STATE| is buried at the bottom of the
list of capabilities. This is done by |get|'s rather clever type:
%
\begin{notyet}
\begin{spec}
get  ::  pi (prf :: SubList ![STATE x] xs).
         prf ~ !findSubListProof ![STATE x] xs
     =>  EffM m xs (UpdateWith ![STATE x] xs prf) x
\end{spec}
\end{notyet}
%
The function |get| takes in a proof that |![STATE x] xs| is a sublist
of |xs|, the list of capabilities in the result type. (|EffM| is a 
generalization of |Eff| that allows for the capabilities to change
during a computation. It lists the ``before'' capabilities and the
``after'' capabilities. |Eff| is just a type synonym for |EffM| with
both lists the same.) Despite taking the proof in as an argument,
|get| requires that the proof be the one found by the |findSubListProof|
function. In this way, the calling code does not need to write the
proof by hand; it can be discovered automatically. However, note that
the proof is |pi|-bound---it is needed at runtime because each capability
is associated with a resource, stored in a list. The proof acts as
an index into that list to find the resource.

In Idris, |get|'s type is considerably simpler: |get :: Eff m ![STATE x] x|.
This works in Idris because of Idris's \emph{implicits} feature, whereby
a user can install an implicit function to be tried in the case of a type
mismatch. In our case here, the list of capabilities in |get|'s type
will not match the larger list in |eval|'s type, triggering a type error.
The \effects/ library provides an implicit lifting operation which does
the proof search I have encapsulated into |findSubListProof|. While it
is conceivable to consider adding such an implicits feature to Haskell,
doing so is well beyond this dissertation. In the case of my translation
of \effects/, the lack of implicits bites, but not in a particularly
damning way; the types of basic operations like |get|
just get a little more involved.

\subsubsection{Example 2: Working with files}

\citet[Section 2.2.5]{algebraic-effects} includes also an example
of how \effects/ can help us work with files. We first define
a |readLines| function that reads all of the lines in a file.
This uses primitive operations |readLine| and |eof|.
%{
%if style == poly
%format SHere = Here
%format SRead = Read
%format FILE_IO = "\id{FILE\_IO}"
%else
%format FILE_IO = "FILE_IO"
%endif
\begin{working}
\begin{code}
readLines  ::  Eff IO ![FILE_IO (OpenFile !Read)] [String]
readLines  =   readAcc []
  where
    readAcc acc = do  e <- eof
                      if (not e)
                         then do  str <- readLine
                                  readAcc (str : acc)
                         else return (reverse acc)
\end{code}
\end{working}

Once again, let's look at the type. The only capability asserted
by |readLines| is the ability to access one file opened for reading.
The implementation is straightforward.

This function is used by |readFile|:
\begin{working}
\begin{code}
readFile :: String -> Eff IO ![FILE_IO (), STDIO, EXCEPTION String] [String]
readFile path 
  = catch  (do  _ <- open path SRead
                Test SHere (raise ("Cannot open file: " ++ path)) $
                  do  lines <- lift readLines
                      close (at _) (at Read)
                      return lines)
           (\ err -> do  putStrLn ("Failed: " ++ err)
                         return [])
\end{code}
\end{working}
%}
