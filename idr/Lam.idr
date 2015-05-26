module Lam

%default total

data Ty : Type where
  Unit : Ty
  (:~>) : Ty -> Ty -> Ty
infixr 0 :~>

data Elem : List a -> a -> Type where
  EZ : Elem (x :: xs) x
  ES : Elem xs x -> Elem (y :: xs) x

data Expr : List Ty -> Ty -> Type where
  Var : Elem ctx ty -> Expr ctx ty
  Lam : Expr (arg :: ctx) res -> Expr ctx (arg :~> res)
  App : Expr ctx (arg :~> res) -> Expr ctx arg -> Expr ctx res
  TT  : Expr ctx Unit

data Val : Ty -> Type where
  LamVal : Expr [arg] res -> Val (arg :~> res)
  TTVal  : Val Unit

shift : Expr ctx ty -> Expr (x :: ctx) ty
shift = go []
  where
    shift_elem : (ctx0 : List Ty) -> Elem (ctx0 ++ ctx) y -> Elem (ctx0 ++ x :: ctx) y
    shift_elem [] x = ES x
    shift_elem (y :: xs) EZ = EZ
    shift_elem (y :: xs) (ES x) = ES (shift_elem xs x)

    go : (ctx0 : List Ty) -> Expr (ctx0 ++ ctx) ty -> Expr (ctx0 ++ x :: ctx) ty
    go ctx0 (Var x) = Var (shift_elem ctx0 x)
    go ctx0 (Lam {arg} x) = Lam (go (arg :: ctx0) x)
    go ctx0 (App x y) = App (go ctx0 x) (go ctx0 y)
    go ctx0 TT = TT

subst : {s : Ty} -> {ctx : List Ty} -> {t : Ty} -> Expr ctx s -> Expr (s :: ctx) t -> Expr ctx t
subst {s} {ctx} e = go []
  where
    subst_var : (ctx0 : List Ty) -> Elem (ctx0 ++ s :: ctx) ty -> Expr (ctx0 ++ ctx) ty
    subst_var [] EZ = e
    subst_var [] (ES x) = Var x
    subst_var (ty :: xs) EZ = Var EZ
    subst_var (y :: xs) (ES x) = shift (subst_var xs x)

    go : (ctx0 : List Ty) -> Expr (ctx0 ++ s :: ctx) ty -> Expr (ctx0 ++ ctx) ty
    go ctx0 (Var x) = subst_var ctx0 x
    go ctx0 (Lam {arg} x) = Lam (go (arg :: ctx0) x)
    go ctx0 (App x y) = App (go ctx0 x) (go ctx0 y)
    go ctx0 TT = TT

apply : Val (arg :~> res) -> Expr [] arg -> Expr [] res
apply (LamVal x) x1 = subst x1 x

partial
eval : [static] Expr [] ty -> Val ty
eval (Var EZ) impossible
eval (Var (ES _)) impossible
eval (Lam x) = LamVal x
eval (App x y) = eval (apply (eval x) y)
eval TT = TTVal

data StepResult : Expr [] ty -> Type where
  Stepped : {e : Expr [] ty} -> (e' : Expr [] ty) -> {solve pf : eval e = eval e'} -> StepResult e
