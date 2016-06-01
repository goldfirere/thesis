(* An attempt to encode Girard's paradox in Coq, just to see what happens. *)

Definition P s := s -> Type.

Definition Bot := forall (p : Type), p.

Definition Not p := p -> Bot.

Definition U := forall (x : Type), ((P (P x) -> x) -> P (P x)).

Definition tau (t : P (P U)) := fun (X : Type) (f : P (P X) -> X) (p : P X) =>
                                  (t (fun (x : U) => p (f (x X f)))).
Set Printing Universes.
Definition sigma (s : U) := s U (fun (t : P (P U)) => tau t).
  (* Error: Universe inconsistency. *)
