
Require Import List.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Definition undefined {A} : A. Admitted.

Inductive Ty : Type :=
| Unit
| Arr : Ty -> Ty -> Ty.

Notation "ty1 :~> ty2" := (Arr ty1 ty2) (at level 11, right associativity).

Inductive Elem : forall A, list A -> A -> Type :=
| EZ : forall {A} {x : A} {xs}, Elem (x :: xs) x
| ES : forall {A} {x : A} {y xs}, Elem xs x -> Elem (y :: xs) x.

Inductive Expr : list Ty -> Ty -> Type :=
| Var : forall ctx ty, Elem ctx ty -> Expr ctx ty
| Lam : forall arg res ctx, Expr (arg :: ctx) res -> Expr ctx (arg :~> res)
| App : forall arg res ctx, Expr ctx (arg :~> res) -> Expr ctx arg -> Expr ctx res
| TT  : forall ctx, Expr ctx Unit.

Inductive Val : list Ty -> Ty -> Type :=
| LamVal : forall arg res ctx, Expr (arg :: ctx) res -> Val ctx (arg :~> res)
| TTVal : forall ctx, Val ctx Unit.

Lemma shift_elem : forall {x y : Ty} {ctx : list Ty} ctx0,
                     Elem (ctx0 ++ ctx) y -> Elem (ctx0 ++ x :: ctx) y.
Proof.
  intros x y ctx ctx0. induction ctx0; simpl.
  * exact ES.
  * intro e. dependent destruction e.
    - exact EZ.
    - apply ES. apply IHctx0. assumption.
Qed.

Lemma shift_go : forall {x ty : Ty} {ctx : list Ty} (ctx0 : list Ty)
                        (e : Expr (ctx0 ++ ctx) ty), Expr (ctx0 ++ x :: ctx) ty.
Proof.
  intros. dependent induction e; simpl.
  * apply Var. apply shift_elem. assumption.
  * apply Lam. rewrite app_comm_cons. apply IHe. apply app_comm_cons.
  * apply App with (arg := arg). assumption. assumption.
  * apply TT.
Qed.

Lemma shift : forall ctx x ty, Expr ctx ty -> Expr (x :: ctx) ty.
Proof.
  intros. apply shift_go with (ctx0 := nil). simpl. assumption.
Qed.

Lemma subst_var : forall {s t : Ty} {ctx : list Ty} (ctx0 : list Ty)
                         (e : Expr ctx s) (v : Elem (ctx0 ++ s :: ctx) t),
                    Expr (ctx0 ++ ctx) t.
Proof.
  induction ctx0; intros e v; simpl.
  * dependent destruction v.
    - exact e.
    - exact (Var v).
  * dependent destruction v.
    - exact (Var EZ).
    - apply shift. apply IHctx0. exact e. exact v.
Qed.

Lemma subst_go : forall {s t : Ty} {ctx : list Ty} (ctx0 : list Ty)
                        (e1 : Expr ctx s) (e2 : Expr (ctx0 ++ s :: ctx) t),
                   Expr (ctx0 ++ ctx) t.
Proof.
  intros. dependent induction e2; simpl.
  * apply (@subst_var s). exact e1. exact e.
  * apply Lam. rewrite app_comm_cons. apply IHe2 with (s0 := s). exact e1.
    apply app_comm_cons.
  * apply App with (arg := arg). apply IHe2_1. exact e1. apply IHe2_2. exact e1.
  * apply TT.
Qed.

Lemma subst : forall {s t : Ty} {ctx : list Ty},
                Expr ctx s -> Expr (s :: ctx) t -> Expr ctx t.
Proof.
  intros. apply (@subst_go s) with (ctx0 := nil). exact X. exact X0.
Qed.`
