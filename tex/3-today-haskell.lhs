%% -*- mode: LaTeX -*-

%if style == newcode
%include rae.fmt
%endif

\chapter{Haskell in 2015}

\begin{proposal}
This section will contain an in-depth description of the various features
of today's Haskell that support programming with dependent types. I include
parts of sections about generalized algebraic datatypes and type families here.
\end{proposal}

\section{Generalized algebraic datatypes}

A critical part of programming with dependency is to have operations on terms
inform the compiler's understanding of the terms' types. Haskell achieves
this today through its generalized algebraic datatypes, or GADTs.

\subsection{Simple example}
Let's start with a small example:
%
\begin{code}
data G a where
  MkGInt   :: G Int
  MkGBool  :: G Bool

frobble :: G a -> a
frobble MkGInt   = 5
frobble MkGBool  = True
\end{code}

In this example, we have a simple GADT, |G|. If a |G a| is built using the
constructor |MkGInt|, then we know |a| must be |Int|. Similarly, when a |G a|
built using |MkGBool|, we know that |a| must be |Bool|.

Accordingly, when |frobble| pattern-matches on a |G a|, we learn what the type
|a| must be. Therefore, on the right-hand side of the pattern-match for
|MkGInt|, we know that |a| is |Int|, and that |5| is a suitable return value.
Similarly, in the branch where we have matched |MkGBool|, we know that |True|
is a suitable return value.

\subsection{Longer example: a strongly typed interpreter}
Here, we return to the motivating example mentioned in \pref{sec:stlc}, where
we build an interpreter for the simply typed lambda calculus. Due to our
use of GADTs, we can be sure that, for example, the evaluation function
preserves types.

Recall the datatypes used to describe types and expressions in our language:
%
%if style == newcode
\begin{code}
data Elem ctx ty
\end{code}
%endif
%
\begin{code}
data Ty :: * ^^ where
  IntTy  :: Ty
  (:~>)  :: Ty -> Ty -> Ty

data Expr :: [Ty] -> Ty -> * ^^ where
  Var  :: Elem ctx ty -> Expr ctx ty
  Lam  :: Expr (arg !: ctx) res -> Expr ctx (arg !:~> res)
  App  :: Expr ctx (arg !:~> res) -> Expr ctx arg -> Expr ctx res
  Lit  :: Int -> Expr ctx !IntTy
\end{code}
%
Let's examine one line of the big-step evaluator function for this
language:
%
\begin{code}
apply :: Val ctx (arg !:~> res) -> Expr ctx arg -> Expr ctx res

eval :: Expr nil t -> Val nil t
eval (App fun arg) = eval (apply (eval fun) arg)
\end{code}
%
%if style == newcode
\begin{code}
eval (Var v) = case v of {}
eval (Lam body) = LamVal body
eval (Lit n) = LitVal n

data Val :: [Ty] -> Ty -> * where
  LitVal :: Int -> Val ctx IntTy
  LamVal :: Expr (arg !: ctx) res -> Val ctx (arg !:~> res)

apply = undefined
\end{code}
%endif
