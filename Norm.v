(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Load "eztactics.v".

Add LoadPath "Listkit" as Listkit.

Require Import Coq.Sets.Image.

Require Import Rewrites.
Require Import Term.

Inductive StrongNorm A R (x:A) :=
  reducts_SN : (forall x', R x x' -> StrongNorm _ R x') -> StrongNorm _ R x.

#[local] Hint Constructors StrongNorm : Norm.

(** Strong normalization: a term is strongly normalizing if all its
    reducts are strongly normalizing.

    The well-foundedness of inductive objects in Coq means that the
    reduction trees are well-founded or strongly-normalizing.
*)

Definition SN := StrongNorm _ RewritesTo.

#[export] Hint Unfold SN : Norm.

#[export] Hint Resolve reducts_SN : Norm.

Lemma SN_Const : SN TmConst.
 apply reducts_SN.
 intros.
 solve by inversion 1.
Qed.

Lemma SN_Var : forall x, SN (TmVar x).
 intros.
 apply reducts_SN.
 intros.
 solve by inversion.
Qed.

(*
Lemma SN_Abs : forall n, SN n -> SN (TmAbs n).
 intros; apply reducts_SN; intros.
 intros ; solve by inversion.
Qed.
*)

#[export] Hint Resolve SN_Const SN_Var (*SN_Abs*) : Norm.

(** If a property is preserved by reduction, then it holds for all
    strongly normalizing terms. *)
Lemma SN_induction P:
  (forall M, (forall M', (M ~> M') -> P M') -> P M) ->
  forall M,
    SN M ->
    P M.
Proof.
 intros IH M H.
 induction H; eauto.
Qed.

(** [Double_SN] holds for a pair of terms iff all of the immediate
    reducts of each one is also [Double_SN]. TODO: I think this is the
    same as each one separately being strongly normalizing, so what do I
    need it for? *)
Inductive Double_SN M N :=
  | both_reducts_sn :
       (forall M', (M ~> M') -> Double_SN M' N)
    -> (forall N', (N ~> N') -> Double_SN M N')
    -> Double_SN M N.

Lemma double_sn_intro :
  forall M, SN M -> forall N, SN N -> Double_SN M N.
Proof.
 intros M SN_M.
 induction SN_M.
 intros N SN_N.
 induction SN_N.
 rename x into M, x0 into N.
 apply both_reducts_sn; auto with Norm.
Qed.

Lemma Double_SN_induction P:
  (forall x y,
    (forall x', (x ~> x') -> P x' y) ->
    (forall y', (y ~> y') -> P x y') -> P x y) ->
  forall x y, Double_SN x y -> P x y.
Proof.
 intros IH x y SN_x_y.
 induction SN_x_y.
 auto.
Qed.

(** An induction principle on pairs of SN terms simultaneously. If a
    relation [P] between terms holds given its holding for every reduct of
    either term, then it holds for all strongly normalizing terms. *)
Lemma SN_double_induction P:
  (forall x y,
    (forall x', (x ~> x') -> P x' y) ->
    (forall y', (y ~> y') -> P x y') -> P x y) ->
  forall x y, SN x -> SN y -> P x y.
Proof.
 intros IH x y SN_x SN_y.
 apply Double_SN_induction; auto.
 apply double_sn_intro; auto.
Qed.

Ltac double_induction_SN M N :=
  cut (M ~>> M); [|auto]; cut (N ~>> N); [|sauto]; pattern N at 2 3, M at 2 3;
  refine (SN_double_induction _ _ N M _ _) ; [ | sauto | sauto].

Ltac double_induction_SN_intro M N :=
  cut (M ~>> M); [|auto]; cut (N ~>> N); [|sauto]; pattern N at 2 3, M at 2 3;
  refine (SN_double_induction _ _ N M _ _) ; [ | sauto | sauto];
  let N' := fresh N "'" in
  let M' := fresh M "'" in
  let IHN := fresh "IH" N in
  let IHM := fresh "IH" M in
  let N_rw_N' := fresh N "_rw_" N' in
  let M_rw_M' := fresh M "_rw_" M' in
  intros N' M' IHN IHM N_rw_N' M_rw_M'.

(** The tactic [redseq_induction M] allows us to prove the current
   goal [P M] by proving that [P] holds for an arbitrary transitive
   reduct of [M], provided that all of ITS immediate reducts have the
   property. *)
Ltac redseq_induction M :=
   cut (M ~>> M); [|auto];
   pattern M at 2 3; (* The reduct and the other position *)
   refine (SN_induction _ _ M _); [
   let M' := fresh M in
     let IH_M := fresh "IH" M in
         let M_to_M' := fresh M "to" M' in
           intros M' IH_M; intros
     | try trivial].

(** Reducing a term transitively preserves its SN status. *)
Lemma Rw_trans_preserves_SN :
  forall M M',
    SN M -> (M ~>> M') -> SN M'.
Proof.
 intros M M' H red.
 induction red.
 - congruence.
 - inversion_clear H; auto with Norm.
 - auto with Norm.
Qed.

#[export] Hint Resolve Rw_trans_preserves_SN : Norm.

(* (        ~>          )      (               )
   (   M ---------> M'  )      (            N  )
   (   |            |   )      (            |  )
   ( f |          f |   )  ->  (          f |  ) -> SN Q -> SN N
   (   |            |   )      (            |  )
   (   V    ~>      V   )      (     ~>>    V  )
   (  f M · · · ·> f M' )      ( Q ------> f N ) *)

(** If we have a function [f] that is compatible with rewriting, then
    for any SN term [Q], if [Q] reduces (transitively) to some [f M],
    and [f M] is SN, then [M] is too. (Oy, that's awkward. Any simpler
    lemma we could use instead?) *)
Lemma SN_embedding f:
  (forall M M', (M ~> M') -> (f M ~> f M')) ->
  forall Q, SN Q ->
      forall M, (Q ~>> f M) ->
          SN M.
(* TODO: I can't believe how hard this was!
   TODO: Wrap this up in something that instantiates Q as f M, which is how we use it. *)
Proof.
 intros H Q H0.
 induction H0.
 rename x into q.
 intros.
 apply reducts_SN.
 assert (H2 : SN (f M)).
  apply Rw_trans_preserves_SN with (M := q); auto with Norm.
 inversion H2.
 intros m' H4.
 lapply (last_step_first_step_lemma _ _ H1 (f m')); [| auto].
 intros [x q_x x_f_m'].
 apply H0 with x; auto.
Qed.


(** Consider terms of the form [g M]. Suppose that every one has all its reducts satisfying either:
    (a) reduct is of the form [g M'] and there is a parallel reduction [f M ~> f M'] or
    (b) reduct is known to be SN.

Then, if some [f M] is SN, the corresponding [g M] is too.

Further, everything about this lemma is relative to some ancestor
term, so it only has to be true for descendents of that ancestor.
*)

Lemma SN_embedding2 A f g:
  forall Q' : Term,
    (forall (M : A) (Z : Term),
       (Q' ~>> g M) ->
       (g M ~> Z) ->
       ({M' : A & ((Z = g M') *
                   (f M ~> f M'))%type}
        + SN Z)) ->
    forall Q : Term, SN Q ->
    forall M : A,
      (Q ~>> f M) ->
      (Q' ~>> g M) ->
      SN (g M).
Proof.
 intros Q' H Q H0.
 induction H0.
 rename x into q.
 intros M Q_def Q'_def.
 apply reducts_SN.
 assert (H2 : SN (f M)) by eauto with Norm.
 inversion H2 as [H3].
 intros m' H4.
 copy (g M ~> m').
 apply H in H4; try auto.
 destruct H4 as [[M' [m'_form f_M_f_M']] | bailout]; auto.
 fold SN.
 lapply (last_step_first_step_lemma _ _ Q_def (f M')); eauto.
 intros [x q_x x_f_m'].
 subst m'.
 eauto.
Qed.

Lemma SN_embedding2' A f g:
    (forall (M : A) (Z : Term),
       (g M ~> Z) ->
       ({M' : A & ((Z = g M') *
                   (f M ~> f M'))%type}
        + SN Z)) ->
    forall M : A,
      SN (f M) ->
        SN (g M).
Proof.
 intros.
 apply SN_embedding2 with (f:=f)(Q:=f M)(Q':=g M).
    intros.
    auto.
   auto.
  auto.
 auto.
Qed.

Lemma SN_context_Proj : forall b M,
                          SN (TmProj b M) -> SN M.
Proof.
 intros b M H.
 apply (SN_embedding (TmProj b)) with (TmProj b M); auto.
Qed.

Lemma SN_context_App_left:
  forall L M, SN (L@M) -> SN L.
Proof.
 intros L M H.
 apply (SN_embedding (fun x => (x @ M))) with (L @ M); auto.
Qed.

(** (Compare Lemma 27) *)
Lemma SN_TmSingle:
  forall M,
    SN M -> SN (TmSingle M).
Proof.
 intros.
 redseq_induction M.
 apply reducts_SN.
 intros.
 inversion H1.
 subst.
 apply IHM; eauto.
Qed.

(** When [R] is reflexive, and transitive, and [R x y] follows from [f x ~> f y],
    and [f] is injective, and any [f x] has all descendants of the form [f x'],
    Then two descendents [M] and [N] with [f x ~>> M ~>> N] are of the form
    [M = f y], [N = f z] with [R y z]. That seems pretty dumb.
    Also I think the assertion on the form of M and N can probably be proven
    independent of the fact that their retracts y and z are related by R.
 *)
Lemma rw_rt_f_induction:
  forall A f x R M N,
    (forall x, R x x) ->
    (forall x y z, R x y -> R y z -> R x z) ->
    (injective _ _ f) ->

    (forall x M, (f x ~>> M) -> {x' : A & M = f x'}) ->
    (forall x y, (f x ~> f y) -> R x y) ->

    (f x ~>> M) ->
    (M ~>> N) ->
    {y : A & M = f y & {z : A & N = f z & R y z}}.
Proof.
 intros A f x R M N refl_P trans_R inj_f X0 X1 H H0.
 induction H0.
 - subst.
   apply X0 in H.
   destruct H.
   exists x0; auto.
   exists x0; auto.
 - assert (f x ~>> n).
   apply Rw_rt_trans with m; auto.
   apply X0 in H.
   apply X0 in H0.
   destruct H.
   destruct H0.
   subst.
   exists x0; auto.
   exists x1; auto.
 - assert (f x ~>> m) by (eapply Rw_rt_trans; eauto).
   assert (f x ~>> n) by (eapply Rw_rt_trans; eauto).
   clon H; clon H0; clon H1.
   apply X0 in H.
   apply X0 in H0.
   apply X0 in H1.
   destruct H.
   destruct H0.
   destruct H1.
   subst.
   exists x0; auto.
   exists x2; auto.
   apply IHRewritesTo_rt1 in H2.
   apply IHRewritesTo_rt2 in H3.
   destruct H2 as [y Ha [z Hb Hc]].
   destruct H3 as [y' Ha' [z' Hb' Hc']].
   apply inj_f in Ha.
   apply inj_f in Hb.
   apply inj_f in Ha'.
   apply inj_f in Hb'.
   subst.
   subst.
   eapply trans_R; eauto.
Qed.
