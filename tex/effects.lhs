%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import Data.Kind ( type (*), Type )
import Data.Nat
import Effects hiding (test)
import Effect.StdIO
import Effect.Exception
import Effect.Random
import Effect.State
import Data.AChar
import Effect.File
import Prelude ( Maybe(..), lookup, (++), (<$>), (<*>), IO
               , not, reverse, ($), FilePath )
import Data.Singletons
import Util.If
import Control.Catchable

type Read = !Read
test = Test

\end{code}

%endif

\def\effects/{\package{Effects}}

\subsection{Algebraic effects}
\label{sec:algebraic-effects}

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

With |eval| in hand, it is straightforward to write the function that
actually can evaluate an expression:
%
\begin{code}
runEval :: Vars -> Expr -> IO Nat
runEval env expr = run (() :> () :> 123 :> env :> Empty) (eval expr)
\end{code}
%
The first argument to the \effects/ library function |run| is an
environment of resources, where each resource is associated with
a capability. While the order of capabilities goes not matter in the
body of |eval|, its order must match up with the order of resources
given when running an |Eff| computation. In this case, the
|EXCEPTION String| and |STDIO| capabilities have no associated resource
(the entries in the environment are both |()|). The |RND|
capability uses a random generation seed (|123| in our case),
and the |STATE Vars| needs the initial state, passed as a parameter to
|runEval|.

Having defined all of the above, we can now observe this interaction:
\begin{quote}
|ghci> runEval [("x", 3)] (Var "x" `Add` Random 12)| \\
\texttt{Random value: 1} \\
\texttt{4}
\end{quote}
In this output, the |4| at the end is the result of evaluating the expression,
which adds the value of |"x"|, |3|, to the pseudo-random number |1|.

\subsubsection{Automatic lifting}
\label{sec:effects-automatic-lifting}

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

The function |readLines| is used by |readFile|:
\begin{working}
\begin{code}
readFile :: String -> Eff IO ![FILE_IO (), STDIO, EXCEPTION String] [String]
readFile path 
  = catch  (do  _ <- open path SRead
                test SHere (raise ("Cannot open file: " ++ path)) $
                  do  lines <- lift readLines
                      close (at Read)
                      return lines)
           (\ err -> do  putStrLn ("Failed: " ++ err)
                         return [])
\end{code}
\end{working}
%
The type of |readFile| is becoming routine: it describes an effectful
computation that can access files (with none open), do input/output,
and raise exceptions. The underlying handler is Haskell's |IO| monad,
and the result of running |readFile| is a list of strings.

The body of this function, however, deserves scrutiny, as the type
system is working hard on our behalf throughout this function.
The first line calls the \effects/ library function |open|, which
uses the |FILE_IO| capability. Here is a simplified version of its
type, where the automatic lifting mechanism (\pref{sec:effects-automatic-lifting})
is left out:
\begin{notyet}
\begin{spec}
open  ::  String -> pi (m :: Mode)
      ->  EffM e ![FILE_IO ()] ![FILE_IO (Either () (OpenFile m))] Bool
\end{spec}
\end{notyet}
%
The function |open| takes the name of a file and whether to open it for
reading or writing. Its return type declares that the |open| operation
starts with the capability of file operations with no open file but
ends with the capability of file operations either with no open file
or with a file opened according to the mode requested. Recall that
|EffM| is a generalization of |Eff| that declares two lists of capabilities:
one before an action and one after it. The |Either| in |open|'s type reflects
the possibility of failure. After all, we cannot be sure that |open| will
indeed result in an open file.\footnote{Readers may be wondering at this
point how \effects/ deals with the possibility of multiple open files.
The library can indeed handle this possibility through listing |FILE_IO|
multiple times in the list of capabilities. \effects/ includes a mechanism
for labeling capabilities (not described here, but implemented in Haskell
and described by \citet{algebraic-effects}) that can differentiate among
several |FILE_IO| capabilities.} The return value of type |Bool| indicates
success or failure.

After running |open|, |readFile| uses |test|, another \effects/ function,
with the following type:
\begin{notyet}
\begin{spec}
test  ::  pi (prf :: EffElem e (Either l r) xs)
      ->  EffM m (UpdateResTyImm xs prf l) xs' t
      ->  EffM m (UpdateResTyImm xs prf r) xs' t
      ->  EffM m xs xs' t
\end{spec}
\end{notyet}
Without looking too closely at that type, we can surmise this:
\begin{itemize}
\item The starting capability set, |xs|, contains an effect with an
|Either l r| resource.
\item The caller of |test| must provide a proof |prf| of this fact.
(|EffElem| is a rather standard datatype that witnesses the inclusion
of some element in a list, tailored a bit to work with capabilities.)
\item The next two arguments of |test| are continuations to pursue
depending on the status of the |Either|. Note that the first works
with |l| and the second with |r|. Both continuations must result in the
same ending capability set |xs'|.
\item The |test| operator itself takes the capability set from |xs|
to |xs'|.
\end{itemize}
In our case, |test| is meant to check the |Either () (OpenFile !Read)|,
stored in the first capability. (|Here| is the proof that the capability
we seek is first in the list.) If the |Either| is |Left|, |raise| an
exception. Otherwise, we know that the |open| succeeded, and the
inner |do| block can work with a capability |FILE_IO (OpenFile !Read)|.

The inner |do| block runs |readLines|, using |lift| because
the type of |readLines| assumes only the one |FILE_IO| capability,
and |readFile| has more than just that. The same automatic proof search
facility described earlier works with explicit |lift|s.

The use of |close| here is again interesting, because omitting it would
be a type error. Here is |close|'s type (again, eliding the lifting
machinery):
\begin{notyet}
\begin{spec}
close :: forall m e. EffM e ![FILE_IO (OpenFile m)] ![FILE_IO ()] ()
\end{spec}
\end{notyet}
It takes an |OpenFile| and closes it. Forgetting this step would be
a type error because |test| requires that both paths result in the same
set of capabilities. The failure path from |test| has no open files at
the end, and so the success path must also end with no open files.
The type of |close| achieves this.

A careful reader will note that we have to specify the |Read| invisible
parameter to |close|. This is necessary to support the automatic lifting
mechanism. Without knowing that it is searching for |FILE_IO (OpenFile Read)|,
it gets quite confused; looking for |FILE_IO (OpenFile m)| is just not
specific enough. It is conceivable that this restriction could be lifted
with a cleverer automatic lifting mechanism or a type-checker plugin~\cite{type-checker-plugins,diatchki-smt-plugin}.

All of the code described above is wrapped in a |catch| in order to deal
with any possible exception; |catch| is not intricately typed and does
not deserve further study here.

Having written |readFile|, we can now use it:
\begin{spec}
printFile :: FilePath -> IO ()
printFile filepath
  =  do  ls <- run (() :> () :> () :> Empty) (readFile filepath)
         mapM_ putStrLn ls
\end{spec}
The return type of |printFile| is just the regular Haskell |IO| monad.
Due to the way GHC's \ext{RebindableSyntax} extension works, |printFile|
must be written in a separate module from the code above in order to access
the usual monadic meaning of |do|.

This example has shown us how the \effects/ not only makes it easy to
mix and match different effects without the quadratic code cost of
monad transformers, but it also helps us remember to release resources.
Forgetting to release a resource has become a type error.

\subsubsection{Example 3: an interpreter for a well-typed imperative language}

The final example with \effects/ is also the culminating example by
\citet[Section 4]{algebraic-effects}: an interpreter for an imperative
language with mutable state. The goal of presenting this example is
simply to show that \effects/ scales to ever more intricate types,
even in its translation to Haskell. Accordingly, I will be suppressing
many details in this presentation. The curious can read the full source
code online.\footnote{\url{https://github.com/goldfirere/thesis/blob/master/effects/Sec4.hs}}

This language, Imp, contains both expressions and statements:
\begin{working}
\begin{spec}
data Ty = ...  -- types in Imp
interpTy :: Ty -> Type  -- consider a |Ty| as a real Haskell |Type|
data Expr  ::  forall n. Vec Ty n -> Ty -> Type where ...
data Imp   ::  forall n. Vec Ty n -> Ty -> Type where ...
\end{spec}
\end{working}
Following the implementation in Idris, my translation uses a deep embedding
for the types, using the datatype |Ty| instead of Haskell's types. This is
purely a design choice; using Haskell's types works just as
well.\footnote{Interestingly, the use of a deep embedding in my implementation
means that I have to label |interpTy| as injective~\cite{injective-type-families}.
Otherwise, type inference fails. Idris's type inference algorithm must
similarly use injectivity to accept this program.}

Expressions and
statements (the datatype |Imp|) are parameterized over a vector of types given
to de Bruijn-indexed variables. Both expressions and statements also produce
an output value, included in their types above. Thus, an expression of
type |Expr g t| has type |t| in the typing context |g|.

Let's focus on the statement form that introduces a new, mutable variable:
%if style == poly
%format :& = "\mathop{{:}{\&}}"
%format :^ = "\mathop{{:}{\string^}}"
%endif
\begin{notyet}
\begin{spec}
data Imp :: forall n. Vec Ty n -> Ty -> Type where
  Let   ::  forall t g u. Expr g t -> Imp (t :& g) u -> Imp g u
  ...
\end{spec}
\end{notyet}
The variable, of type |t|, is given an initial value by evaluating the
|Expr g t|. The body of the |Let| is an |Imp (t :& g) u|---that is, a
statement of type |u| in a context extended by |t|. (The operator |:&|
is the |cons| operator for |Vec|, here.)

Here is how such a statement is interpreted:
\begin{notyet}
\begin{spec}
interp :: forall g t. Imp g t -> Eff IO ![STDIO, RND, STATE (Vars g)] (!interpTy t)
interp (Let (at t') e sc)
  = do  e' <- lift (eval e)
        vars <- get (at (Vars g))
        putM (at (Vars g)) (e' :^ vars)
        res <- interp sc
        (_ :^ vars') <- get (at (Vars (t' :& g)))
        putM (at (Vars (t' :& g))) vars'
        return res
\end{spec}
\end{notyet}
%}
I will skip over most of the details here, making only these points:
\begin{itemize}
\item It is necessary to use the $\at$ invisibility override (\pref{sec:visible-type-pat}) several times so that the automatic lifting mechanism knows what to
look for. An alternatives to the approach seen here include using explicit labels
on capabilities (see \citet[Section 2.1.2]{algebraic-effects}), writing down
the index of the capability desired, or implementing a type-checker plugin to
help do automatic lifting.
\item The |putM| function (an operation on |STATE|) changes the type of
the stored state. In this case, the stored state is a vector that is
extended with the new variable. We must, however, remember to restore
the original state, as otherwise the final list of capabilities would be
different than the starting list, a violation of |interp|'s type.
(Recall that |Eff|, in |interp|'s type, requires the same final capability
set as its initial capability set.)
\item The |eval| function (elided from this text) uses a smaller set
of capabilities. Its use must be |lift|ed.
\end{itemize}
Despite the ever fancier types seen in this example, Haskell still holds
up. The requirement to specify the many invisible arguments (such as
|at (Vars g)|) is indeed regrettable; however, I feel confident that some
future work could resolve this pain point.

\subsubsection{Conclusion}

The \effects/ library is a major achievement in Idris and shows some
of the power of dependent types for practical programming. I have shown
here that this library can be ported to Dependent Haskell, where it remains
just as useful. Perhaps as Dependent Haskell is adopted, more users will
prefer to use this approach over monad transformers.

%%  LocalWords:  newcode rae fmt StdIO AChar Util endif AST Expr Val Var Vars
%%  LocalWords:  eval Eff RND var val poly SHere SRead readLines putStrLn prf
%%  LocalWords:  readFile EffM OpenFile EffElem UpdateResTyImm printFile mapM
%%  LocalWords:  filepath RebindableSyntax Ty interpTy Vec interp putM
