Add LoadPath "Listkit" as Listkit.

Require Import Omega.

Require Import Continuation.
Require Import Rewrites.
Require Import Norm.
Require Import Term.

(** * More Induction Principles on Reduction Sequences *)

(** These require knowledge of Continuation.v, so can't be placed in Norm.v *)

(** Continuations have their own "strong normalization" on their own reduction
    rule. *)

Definition Krw_norm := StrongNorm _ Krw.

Inductive Triple_SN K M N :=
  | triple_sn :
       (forall K', (Krw K K') -> Triple_SN K' M N)
    -> (forall M', (M ~> M') -> Triple_SN K M' N)
    -> (forall N', (N ~> N') -> Triple_SN K M N')
    -> Triple_SN K M N.

Lemma triple_induction_via_TripleSN_scoped P:
  forall K0 M0 N0,
  (forall K M N,
     Krw_rt K0 K -> (M0 ~>> M) -> (N0 ~>> N) ->
        (forall K',  (Krw K K') -> P K' M N)
     -> (forall M',  (M ~> M') ->  P K M' N)
     -> ((forall N', (N ~> N') ->  P K M N'))
     -> P K M N)
  ->
    Triple_SN K0 M0 N0 -> P K0 M0 N0.
Proof.
 intros K0 M0 N0 IH SN_K0_M0_N0.
 induction SN_K0_M0_N0.
 apply IH; auto.
 intros; apply X; auto.
 intros; apply IH; eauto.
 intros; apply X0; auto.
 intros; apply IH; eauto.
 intros; apply X1; auto.
 intros; apply IH; eauto.
Qed.

Lemma Triple_SN_intro:
  forall K, Krw_norm K -> forall M, SN M -> forall N, SN N -> Triple_SN K M N.
Proof.
 intros K SN_K.
 induction SN_K.
 intros M SN_M.
 induction SN_M.
 intros N SN_N.
 induction SN_N.
 constructor; sauto.
Qed.

Lemma triple_induction_scoped P:
  forall K0 M0 N0,
  (forall K M N,
     Krw_rt K0 K -> (M0 ~>> M) -> (N0 ~>> N) ->
        (forall K',  (Krw K K') -> P K' M N)
     -> (forall M',  (M ~> M') ->  P K M' N)
     -> ((forall N', (N ~> N') ->  P K M N'))
     -> P K M N)
  ->
    Krw_norm K0 -> SN M0 -> SN N0 -> P K0 M0 N0.
Proof.
 intros K0 M0 N0 IH SN_K0 SN_M0 SN_N0.
 apply triple_induction_via_TripleSN_scoped; auto.
 apply Triple_SN_intro; auto.
Qed.

Lemma Krw_rt_preserves_SN :
  forall K K' M,
    Krw_rt K K' -> SN (plug K M) -> SN (plug K' M).
Proof.
 intros.
 eauto using Rw_trans_preserves_SN, Krw_rt_Rw_rt.
Qed.

Lemma Krw_preserves_SN :
  forall K K' M,
    Krw K K' -> SN (plug K M) -> SN (plug K' M).
Proof.
 intros.
 eauto using Rw_trans_preserves_SN.
Qed.

Lemma Krw_norm_from_SN:
  forall M, SN M -> forall K X, (M ~>> plug K X) -> Krw_norm K.
Proof.
 intros Q H.
 induction H.
 constructor; fold Krw_norm.
 intros.
 eapply last_step_first_step_lemma in H0 as [x0 r r0]; eauto.
Qed.

(** (Lemma 26) *)
Lemma SN_K_M_SN_K_Null:
  forall K M,
    SN (plug K M) ->
    SN (plug K TmNull).
Proof.
 induction K using Ksize_induction_strong.
 rename H into IHK.
 intros M H0.
 apply SN_embedding2 with
     (f := fun k => plug k M)
     (g := fun k => plug k TmNull)
     (Q := plug K M)
     (Q' := plug K TmNull); try auto.
 intros K0 Z H2 H3.

 clone H3.
 apply K_TmNull_rw in H3 as [[K_shorter H1a [K' Ksize_K' H1b]] | [K' H1a H1b]].
 (* Case [plug K0 TmNull] drops a frame. *)
  right.
  subst.

  (* XXX this is terribly ugly. must be a simpler way *)
  assert (relK_rt K K_shorter).
   assert (relK_rt K (appendK K' K_shorter)).
    apply K_TmNull_relK_rt.
    auto.
   apply trans with (K' := appendK K' K_shorter).
    auto.
   apply relK_rt_appendK.
  apply magic with (M:=M) in H1; auto.

  destruct H1 as [M' SN_M'].

  apply IHK with (M:=M'); auto.
  apply Rw_rt_conserves_Ksize in H2.
  rewrite Ksize_appendK in H2.
  omega.

 (* Case K0 ~> K' *)
 left.
 exists K'.
 firstorder.
Qed.

Hint Unfold SN.

Lemma Krw_rt_relK_rt:
  forall K K', Krw_rt K K' -> relK_rt K K'.
Proof.
  intros.
  induction H.
  subst.
  apply refl.
  apply step.
  apply rw; auto.
  eapply trans; eauto.
Qed.

(** (Lemma 30) *)
Lemma SN_K_Union:
  forall K,
  forall M N, SN (plug K M) -> SN (plug K N) -> SN (plug K (TmUnion M N)).
Proof.
 intros K'.
 pattern K'.
 apply Ksize_induction_strong; intros.

 clear K'.

 assert (SN M) by (eauto using SN_push_under_k).
 assert (SN N) by (eauto using SN_push_under_k).
 assert (Krw_norm K) by (eauto using Krw_norm_from_SN).
 apply triple_induction_scoped with (K0 := K) (M0 := M) (N0 := N); auto.
 intros.

 apply reducts_SN.
 intros Z H_rw.

 destruct K0.
 - simpl in *.
   unfold SN in *.
   inversion H_rw; subst; auto.

 - simpl in H_rw.

   apply three_ways_to_reduce_at_interface in H_rw as
       [[[[[M' Z_def rw] | [K' Z_def rw]] | [H' [K' [M' ? [? ? H_bogus]]]]] | ?] | ?].
   * (* Case: rw is within TmBind (TmUnion M N) t *)
     subst.
     inversion rw; subst.
     -- (* Case: body of (TmBind (TmUnion _ _ )) is TmNull; collapses *)
       assert (plug K M ~>> plug (Iterate TmNull K0) M).
       { apply Krw_rt_Rw_rt; auto. }
       (* To do: Krw_rt_Rw_rt and plug_rw_rt are very similar, but with very different names. *)
       assert (plug (Iterate TmNull K0) M ~> plug K0 TmNull).
       simpl.
       auto.
       assert (plug K M ~>> plug K0 TmNull).
       eauto.
       eapply Rw_trans_preserves_SN.
       exact H0.
       auto.
     -- (* Case: rw is zippering TmUnion thru TmBind _ _ *)
       assert (Ksize K0 < Ksize K).
       { assert (Ksize (Iterate t K0) <= Ksize K).
         { apply Krw_rt_conserves_Ksize with (K := K); auto. }
         simpl in *; omega. }
       apply H; auto.
       ** eapply plug_SN_rw_rt with (TmBind M t); auto.
          change (SN (plug (Iterate t K0) M)).
          eauto using Krw_rt_preserves_SN.
       ** eapply plug_SN_rw_rt with (TmBind N t); auto.
          change (SN (plug (Iterate t K0) N)).
          eauto using Krw_rt_preserves_SN.
     -- admit.
     -- (* Case: rw is within TmUnion _ _ *)
       unfold SN in *.
       inversion H14; subst; seauto.

     -- (* Case: rw is within t of TmBind (TmUnion M N) t *)
        change (SN (plug (Iterate n' K0) (TmUnion M0 N0))).
        assert (Krw (Iterate t K0) (Iterate n' K0)).
        ** unfold Krw.
           simpl.
           intros.
           apply Rw_under_K.
           eauto.
        ** apply H8.
           sauto.

   (* Case: rw is within K *)
   * subst.
     change (SN (plug (Iterate t K') (TmUnion M0 N0))).
     apply H8; auto.
   * (* Case: M is not a bind but it consumes a K frame. *)
     refute.
     unfold not in *; eauto using H_bogus.
     apply NotBind_TmBind in H_bogus; auto.

   * destruct s as [K' Zeq [K'' K0eq]].
     subst.
     assert (relK_rt K K').
     -- assert (relK_rt K (Iterate t (appendK K'' (Iterate TmNull K')))).
        ** apply Krw_rt_relK_rt; auto.
        ** assert (relK_rt (Iterate t (appendK K'' (Iterate TmNull K'))) K').
           --- eapply trans.
               *** apply step.
                   apply strip with t.
                   eauto.
               *** assert (relK_rt (Iterate TmNull K') K').
                   apply step; eapply strip; eauto.
                   assert (relK_rt (appendK K'' (Iterate TmNull K')) (Iterate TmNull K')).
                   eapply relK_rt_appendK.
                   eauto.
           --- eauto.
     -- destruct (magic _ _ H11 M H0).
        apply SN_K_M_SN_K_Null with x.
        auto.

   * (* Case: M is a TmBind and we assoc with the context. *)
     destruct s as [L [L' ? [K' [N' Ha Hb]]]].
     inversion e.
     subst.
     rewrite reverse_plug_defn.
     apply H.
     -- simpl.
        apply Krw_rt_conserves_Ksize in H5.
        simpl in *.
        omega.
     -- apply Krw_preserves_SN with (Iterate L' (Iterate N' K')).
        { apply assoc_in_K. }
        apply Krw_rt_preserves_SN with K; auto.
        apply Rw_trans_preserves_SN with (plug K M); auto.
        apply Rw_rt_under_K; auto.
     -- apply Krw_preserves_SN with (Iterate L' (Iterate N' K')).
        { apply assoc_in_K. }
        apply Krw_rt_preserves_SN with K.
        auto.
        apply Rw_trans_preserves_SN with (plug K N).
        { auto. }
        { apply Rw_rt_under_K; auto. }
Admitted.

Lemma prefix_Krw_norm:
  forall K' K,
    prefix K' K -> Krw_norm K -> Krw_norm K'.
Proof.
  intros.
  revert K' H.
  induction H0; intros K' H1.
  constructor; intros KZ H2.
  destruct (prefix_breakdown _ _ H1) as [K1 K0eq].
  subst.
  assert (H3: Krw (appendK K1 K') (appendK K1 KZ)).
  apply Krw_appendK; auto.
  pose (H _ H3).
  apply k.
  apply prefix_appendK.
  auto.
Qed.

Lemma Krw_norm_SN:
  forall K,
    Krw_norm K -> SN (plug K TmNull).
Proof.
  induction K using Ksize_induction_strong.
  - intros.
    clone H0.
    induction H0.
    constructor.
    intros.
    apply K_TmNull_rw in H2.
    firstorder; subst.
    * apply H.
      rewrite Ksize_appendK.
      omega.
      apply prefix_Krw_norm with (appendK x1 x0).
      apply prefix_appendK.
      auto.
      auto.
    * apply H0; auto.
      (* seems silly *)
      assert (Ksize x0 <= Ksize x).
      apply Krw_rt_conserves_Ksize.
      eauto.
      intros.
      apply H.
      omega.
      auto.
      inversion H1.
      apply H2.
      auto.
Qed.
