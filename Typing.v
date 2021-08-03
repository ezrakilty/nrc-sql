(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Add Rec LoadPath "Listkit" as Listkit.

Require Import List.
Require Import Term.

Load "eztactics.v".

Require Import Listkit.NthError.

Hint Rewrite app_comm_cons : list.

(** Weaken a typing derivation by extending its environment
    and it still holds. *)
Lemma Weakening :
  forall env' tm ty env, Typing env tm ty ->
    Typing (env++env') tm ty.
Proof.
 induction tm; intros ty env tp; inversion tp; eauto with NthError.
  apply TAbs.
  autorewrite with list.
  seauto.
 apply TBind with s.
  apply IHtm1; sauto.
 autorewrite with list.
 apply IHtm2; sauto.
Qed.

(** Special case of weakening for closed terms. *)
Lemma Weakening_closed :
  forall tm ty env, Typing nil tm ty -> Typing env tm ty.
Proof.
 intros tm ty env H.
 replace env with (nil ++ env); auto using Weakening.
Qed.

#[export]
Hint Resolve Weakening_closed.
