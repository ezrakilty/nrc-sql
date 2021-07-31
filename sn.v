(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Load "eztactics.v".

Add LoadPath "Listkit" as Listkit.

Require Import Arith.
Require Import Lia.
Require Import List.

Require Import Listkit.logickit.
Require Import Listkit.NthError.
Require Import Listkit.Foreach.
Require Import Listkit.Sets.
Require Import Listkit.AllType.
Require Import Listkit.listkit.

(* Add LoadPath ".". *)

Require Import Term.
Require Import Shift.
Require Import Subst.
Require Import Rewrites.
Require Import Norm.
Require Import Typing.
Require Import Monomorphism.
Require Import OutsideRange.
Require Import Continuation.
Require Import Knorm.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import Setoid.
Require Import Coq.Program.Basics. (* TODO: What's this for?? *)
Require Import Bool.

(* Set Loose Hint Behavior Strict. *)

Hint Rewrite app_comm_cons : list.

Definition set_remove := Listkit.Sets.set_remove.

(* TODO Grumble, grumble. Coq makes macros of this sort useless. *)
(* Definition nat_set_map := set_map (A:=nat) eq_nat_dec.
   Hint Transparent nat_set_map.
   Hint Unfold nat_set_map. *)

#[local] Hint Resolve subst_env_compat_rw_rt : core.

(**
* Embeddings

 When we have a form of term, specified by g, whose reductions are
all "found within" the corresponding form f, then if we have an
example SN term in the image of f, the corresponding term in g's image
is also SN.

The lemma also offers the possibility that some reducts of g-form
terms are not g-form terms, but then they must be shown to be SN by
some other means.
*)
(* TO DO: currently unused, but seems like it would be useful for some other lemmas. *)
Lemma SN_embedding3 (f g : Continuation -> Term -> Term -> Term):
  (* TODO: Where we apply this lemma, we need to know that g K M N is a descendent
     of something in order to prove SN Z. How do we narrow the scope of the first premise? *)
  (forall K M N Z, (g K M N ~> Z) ->
             {K' : Continuation & {M' : Term & {N' :Term & Z = g K' M' N'}}} + (SN Z)) ->
  (forall K M N K' M' N', (g K M N ~> g K' M' N') -> (f K M N ~> f K' M' N')) ->
  forall Q, SN Q ->
            forall K M N,
              (Q ~>> f K M N) -> SN (g K M N).
Proof.
 intros Hz H0 Q H1.
 induction H1.
 rename x into q.
 intros K M N H2.
 apply reducts_SN.
 intros.
 assert (SN (f K M N)).
  eauto.
 inversion H3.
 pose (H6 := Hz _ _ _ _ H1).
 inversion H6 as [[K' [M' [N' def_m']]] | SN_m']; auto.

 subst.
 pose (H0 _ _ _ _ _ _ H1).
 lapply (last_step_first_step_lemma _ _ H2 (f K' M' N')); auto.
 intros [x q_to_x x_to_f_K'_M'_N'].
 apply H with x; solve [auto].
Qed.

(******************************** REDUCIBILITY ********************************)

Set Universe Polymorphism.

(** * Reducibility *)
Fixpoint Reducible (tm:Term) (ty:Ty)  {struct ty} : Type :=
  (** To be reducible, a term ... *)
  (Typing nil tm ty * (** ... must be well-typed at ty and *)
  match ty with
  | TyBase => SN tm (** ... at unit type, strongly normalizes *)
  | TyPair s t =>
    Reducible (TmProj false tm) s * Reducible (TmProj true tm) t
      (** ... at pair type, the results of both projections are reducible. *)
  | TyArr s t =>
    (forall l (s_tp:Typing nil l s),
       Reducible l s ->
        Reducible (TmApp tm l) t)
      (** ... at arrow type, must give a reducible term when applied
           to any reducible term. *)
  | TyList s =>
      let ReducibleK (K : Continuation) (T:Ty) :=
          forall M,
            Reducible M T ->
            SN (plug (TmSingle M) K)
      in
      forall K, ReducibleK K s -> SN (plug tm K)
      (** ... at list type, is SN when placed in any reducible continuation. *)
  end)%type.

(** We say that an environment is reducible when it is a list of closed terms, together
with types, and each one is reducible at the corresponding type. *)
Fixpoint env_Reducible Vs Ts : Type :=
  match Vs, Ts with
    | nil, nil => True%type
    | V::Vs, T::Ts => (Reducible V T * env_Reducible Vs Ts)%type
    | _, _ => False
  end.

(** *)

Lemma Reducible_welltyped_closed :
  forall tm ty, Reducible tm ty -> Typing nil tm ty.
Proof.
  destruct ty; firstorder auto.
Qed.

#[local] Hint Immediate Reducible_welltyped_closed : Reducible.

(** The Rewrites relation preserves reducibility. (Lemma 22) *)
Lemma Rw_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~> M') -> Reducible M' T.
Proof.
 induction T; simpl.
 - firstorder using Rw_preserves_types.
   inversion b; solve [auto].
 - firstorder using Rw_preserves_types.
 - firstorder using Rw_preserves_types.
 - intros.
   split; eauto using Rw_preserves_types with Reducible.
   intros.
   assert (H2 : SN (plug M K)) by firstorder.
   inversion H2 as [H3].
   apply (H3 (plug M' K)).
   apply Rw_under_K.
   auto.
Qed.

(** The reflexive-transitive Rewrites relation preserves reducibility,
    and likewise for continuations and their reduction and reducibility predicates. *)
Lemma Rw_rt_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~>> M') -> Reducible M' T.
Proof.
 intros T M R M' red.
 induction red; subst; eauto using Rw_preserves_Reducible.
Qed.

#[local] Hint Resolve Rw_rt_preserves_Reducible : Reducible.

Lemma Krw_preserves_ReducibleK :
  forall T K, ReducibleK Reducible K T -> forall K',
      Krw K K' -> ReducibleK Reducible K' T.
Proof.
 unfold ReducibleK.
 intros.
 destruct (X M X0).
 auto.
Qed.

(* TODO: This seems to be a cheesy way of helping the Reducible_properties.
Afterwards, one of the premises is always true, so we can simplify it. *)
Lemma ReducibleK_Krw_norm_helper:
  forall T K, ReducibleK Reducible K T ->
              {M : Term & Reducible M T} ->
              Krw_norm K.
Proof.
 unfold ReducibleK.
 intros T K X X0.
 destruct X0.
 eauto using Krw_norm_from_SN.
Qed.

(************************** Reducibility Properties **************************)

(** * Reducibility Properties *)

(** The [Reducible] predicate has these important properties which
    must be proved in a mutually-inductive way. They are:
      1. Every type has a [Reducible] term,
      2. Every [Reducible] term is strongly normalizing.
      3. If [M] is a neutral term at type [T], and all of its reducts
         are [Reducible], then it is itself [Reducible].
   Below, we split these out into separate lemmas.
*)
(* TODO: A little messy. Clean up. *)
Lemma Reducible_properties:
  forall T,
    {tm : Term & Reducible tm T} *
    (forall tm, Reducible tm T -> SN tm) *
    (forall M,
      Neutral M -> Typing nil M T ->
      (forall M', (M ~> M') -> Reducible M' T)
      -> Reducible M T).
Proof.
 induction T.
 (* Case TyBase *)
    splitN 3.
    (* Exists a Reducible term at TyBase *)
      simpl; seauto.
    (* Reducible -> SN *)
     simpl.
     tauto.
    (* Neutral terms withdraw *)
    unfold Reducible in *.
    intuition (apply reducts_SN).
    solve [firstorder].

 (* Case TyPair *)
    splitN 3.
    (* Case: exists a reducible term *)
     destruct IHT1 as [[[M M_red] Reducible_SN_T1] Neutral_Reducible_T1].
     destruct IHT2 as [[[N N_red] Reducible_SN_T2] Neutral_Reducible_T2].
     exists (TmPair M N).
     simpl.
     split; [auto with Reducible | ].

     (* Case: When continuation frames (left & right projections) are applied, a
        reducible term is formed. *)
     split.

     (* Case: left projection *)
     (* TODO: double_induction_SN needs us to prove that an arbitrary
        transitive reduct of the term is reducible; but I think it
        would be fine to prove just that the term itself is so. *)
      double_induction_SN_intro M N.
      (* Because (TmProj _ _) is Neutral, it's sufficient to show that all its
         reducts are reducible. *)
      apply Neutral_Reducible_T1; [seauto | solve [eauto with Reducible] | ].
      intros Z H.
      inversion H.
      (* Case: <M', N'> itself reduces *)
       subst.
       inversion H3.
       (* Case: reduction in rhs *)
        subst m1 n m2.
        apply IHM; seauto.
       (* Case: reduction in lhs *)
       subst m n1 m2.
       apply IHN; seauto.
      (* Case: The reduct is at the head; we project. *)
      subst m n Z.
      solve [eauto with Reducible].

     (* Case: right projection *)
     (* TODO: refactor between the TmProj true / TmProj false cases. *)
     double_induction_SN_intro M N.
     (* Because (TmProj _ _) is Neutral, it's sufficient to show that all its
        reducts are reducible. *)
     apply Neutral_Reducible_T2; [seauto | | ].
     (* TODO: why does the TProj1 case go with seauto but this needs me
         to tell is what lemma to use? *)
      apply TProj2 with T1; solve [eauto with Reducible].
     intros Z H.
     inversion H.
     (* Case: <M', N'> itself reduces *)
      subst.
      inversion H3.
       subst m1 n m2.
       apply IHM; seauto.
      subst m n1 m2.
      apply IHN; seauto.
     (* Case: The reduct is at the head; we project. *)
     subst m n Z.
     solve [eauto with Reducible].

   (* Case: Reducible pair-type terms are strongly normalizing *)
    simpl.
    intuition.
    assert (SN (TmProj false tm)) by auto.
    eapply SN_context_Proj; seauto.

   (* Case: Neutral terms at pair type whose reducts are reducible are
      themselves reducible (reducibility "withdraws"). *)
   intros M M_Neutral M_Typing M_reducts_Reducible.
   destruct IHT1 as [[? ?] l_withdraws].
   destruct IHT2 as [[? ?] r_withdraws].
   simpl. (* this is only true if both destructors (projections) are reducible. *)
   split; [sauto | ].
   (* Split into left and right projections. *)
   split; [apply l_withdraws | apply r_withdraws]; eauto.
   (* Case: left projection. *)
    intros M' H. (* Consider all reducts of the projection. *)
    inversion H.
    (* Case: The reduction is in the subject term. *)
     pose (M_reducts_Reducible m2 H3). (* Then the subject's reduct is Reducible. *)
     simpl in r.
     solve [intuition]. (* Which by definition entails our goal. *)
    (* Case: The reduction is at the head; it is the projection. But the subject
             being neutral, it is not a pair, so contradiction. *)
    subst m M.
    solve [inversion M_Neutral].
   (* Case: right projection. *)
   intros M' H.
   inversion H.
    pose (r := M_reducts_Reducible m2 H3).
    simpl in r.
    solve [intuition].
   subst n M.
   solve [inversion M_Neutral].

  (* Case TyArr *)
  splitN 3.
  (* Exists a reducible term at T1->T2 *)
    destruct IHT2 as [[[N N_Red] Red_T2_tms_SN] IHT2_Red_neutral_withdraw].
    (* Given any term at T2, we can abstract it with a dummy argument.
       (shift 0 1) gives us uniqueness of the argument. *)
    exists (TmAbs (shift 0 1 N)).
    split.
    (* The dummy abstraction has the appropriate type. *)
     solve [auto with Reducible Shift].
    (* It is reducible at -> type; it applied to any reducible term gives
       a reducible application. *)
    intros M M_tp M_Red.
    assert (SN N) by auto.
    destruct IHT1 as [[_ Red_T1_tms_SN] _].
    assert (SN M) by auto.
    pattern N, M.
    (* TODO: The double redseq induction pattern. Abstract out! *)
    double_induction_SN_intro M N.
    (* We'll show that all reducts are reducible. *)
    apply IHT2_Red_neutral_withdraw; eauto.
     apply TApp with T1; solve [eauto with Reducible Shift].
    intros M'' red.
    (* Take cases on the reductions. *)
    inversion red as [ | ? Z ? redn_Z | | | | | | | | | | | | | | | | | | | | | | |] ; subst.
    (* beta reduction *)
       (* BUG: should be able to put these all as args to congruence. *)
       pose subst_dummyvar; pose subst_nil; pose unshift_shift.
       replace (unshift 0 1 (subst_env 0 (shift 0 1 M' :: nil) (shift 0 1 N')))
         with N' by congruence.
       apply Rw_rt_preserves_Reducible with N; sauto.
    (* Reduction of the function position. *)
      inversion redn_Z.
      subst Z.
      destruct (shift_Rw_inversion _ _ _ H2) as [N'' N''_def N'0_rew_N''].
      subst n'.
      apply IHN; seauto.
    (* Reduction of the argument position. *)
     apply IHM; seauto.

  (* Reducibile S->T terms are SN. *)
   intros M M_red.
   destruct M_red as [M_tp M_applied_Red].
   destruct IHT1 as [[[X Red_X] _] _].
   assert (Reducible (M@X) T2).
    apply M_applied_Red; solve [eauto with Reducible].
   assert (SN (M@X)).
    solve [firstorder] (* Finds the needed lemma in IHT2 *).
   apply SN_context_App_left with X; sauto.

  (* Reducible Neutral withdraw for (->) *)
  intros M Neutral_M M_tp M_reducts_Reducible.
  simpl.
  split; [auto|].
  intros L L_tp L_Red.
  apply IHT2; [sauto|seauto|].
  (* Now to show that all the reducts of the application M@L are reducible. *)
  intros M_L_reduct H.
  assert (X : forall L', (L ~>> L') -> Reducible (TmApp M L') T2).
   intros L' L_redto_L'.
   assert (SN L').
    apply Rw_trans_preserves_SN with L; auto.
    apply IHT1; auto.
   redseq_induction L'.
   apply IHT2; auto.
    seauto (* typing *).
   intros Z Z_red.
   (* Take cases on the reduction M@M0 ~> Z *)
   inversion Z_red.
   (* Beta-reduction case: bogus because M is neutral. *)
     subst.
     solve [inversion Neutral_M].
   (* Left of (@) case: easy from M_reducts_Reducible. *)
    subst m1 n.
    assert (Reducible_m2: Reducible m2 (TyArr T1 T2)).
     apply M_reducts_Reducible; sauto.
    simpl in Reducible_m2.
    apply Reducible_m2; solve [eauto with Reducible].
   (* Right of (@) case: by inductive hypothesis. *)
   rename n2 into L''.
   apply IHL'; seauto.
  assert (Reducible (M@L) T2).
   apply X; sauto.
  solve [eauto with Reducible].

 (* Case TyList *)
 destruct IHT as [[[N N_Red] Red_T_tms_SN] IHT_Red_neutral_withdraw].
 splitN 3.
 (* Existence of a reducible term. *)
   exists (TmSingle N).
   simpl.
   solve [auto with Reducible].
 (* Reducible terms are strongly normalizing. *)
  simpl.
  intros tm X.
  destruct X as [X0 X1].
  apply (X1 nil).
  simpl.
  intros M H.
  apply SN_TmSingle; sauto.
 (* Reducible Neutral Withdrawal for list terms. *)
 intros.
 simpl.
 split; auto.
 intros.
 change (ReducibleK Reducible K T) in X0.
 assert (Krw_norm K).
  apply ReducibleK_Krw_norm_helper with T; seauto.

 induction H1.
 constructor.
 intros m' H3.
 clone H3.
 apply Neutral_Lists in H3 as [[[M' s1 s2] | [K1 s1 s2]] | [K' eq [K'' xeq]]]; [ | | | auto].
 - subst.
   apply X; auto.

 - subst.
   apply X1; auto.
   rename x into K.
   apply Krw_preserves_ReducibleK with K; auto.

 - subst.
   assert (Krw_norm K').
   eapply prefix_Krw_norm.
   assert (prefix K' (appendK K'' K')).
   apply prefix_appendK; auto.
   apply H2.
   unfold Krw_norm.
   constructor.
   auto.
   apply Krw_norm_SN.
   auto.
Qed.

(** Now we extract the three lemmas in their separate, useful form. *)

(** Every reducible term is strongly normalizing. (Lemma 21) *)
Lemma Reducible_SN:
 forall ty, forall tm, Reducible tm ty -> SN tm.
Proof.
 firstorder using Reducible_properties.
Qed.

#[local] Hint Resolve Reducible_SN : SN.

(** Every neutral term whose reducts are all [Reducible] is itself [Reducible].
    (Lemma 25) *)
Lemma Neutral_Reducible_withdraw :
  forall T M,
    Neutral M ->
    Typing nil M T ->
    (forall M', (M ~> M') -> Reducible M' T)
    -> Reducible M T.
Proof.
 firstorder using Reducible_properties.
Qed.

(** Every type has a [Reducible] term. (Lemma 20) *)
Lemma Reducible_inhabited:
  forall T,
  {tm : Term & Reducible tm T}.
Proof.
 intros T.
 destruct (Reducible_properties T) as [[H _] _].
 auto.
Qed.

(** Reducible continuations are themselves normalizing. *)
Lemma ReducibleK_Krw_norm:
  forall T K, ReducibleK Reducible K T ->
              Krw_norm K.
Proof.
 intros.
 eauto using ReducibleK_Krw_norm_helper, Reducible_inhabited.
Qed.

(** Extract a reducibility witness from a list of them, by index. *)
(* XXX should be a direct consequence of env_Reducible's definition, if it were
defined in terms of [zip] and [and]. *)
Lemma Reducible_env_value:
  forall Vs Ts x V T,
    env_Reducible Vs Ts ->
    value V = nth_error Vs x ->
    value T = nth_error Ts x ->
    Reducible V T.
Proof.
 induction Vs; intros.
 - exfalso.
   destruct x; simpl in *; easy.
 - destruct Ts.
   { simpl in X; contradiction. }
   destruct X.
   destruct x; simpl in *.
   * inversion H0.
     inversion H.
     auto.
   * eauto.
Qed.

(** * Reducibility of specific term types. *)

(** (Lemma 28) *)
Lemma lambda_reducibility:
  forall N T S,
  forall (Ts : list Ty) Vs,
    Typing (S::Ts) N T ->
    env_typing Vs Ts ->
    env_Reducible Vs Ts ->
    (forall V,
      Reducible V S ->
      Reducible (subst_env 0 (V::Vs) N) T) ->
    Reducible (subst_env 0 Vs (TmAbs N)) (TyArr S T).
Proof.
 intros N T S Ts Vs N_tp Vs_tp Vs_red H.
 split.

 (* Typing *)
  solve [eauto].

 (* Reducibility *)
 intros P P_tp P_red.

 simpl.
 replace (map (shift 0 1) Vs) with Vs
   by (symmetry; eauto with Shift).

 assert (SN P) by eauto with SN.
 set (N'' := subst_env 1 Vs N).
 assert (SN_N'' : SN N'').
  assert (forall V, Reducible V S -> SN (subst_env 0 (V::nil) N'')).
   intros.
   apply Reducible_SN with T.
   subst N''.
   rewrite subst_env_concat with (env:=S::Ts).
    apply H; auto.
   simpl.
   apply Reducible_welltyped_closed in X.
   apply env_typing_intro; auto.
  destruct (Reducible_inhabited S) as [V V_Red].
  pose (X V V_Red).
  apply SN_embedding with (f := subst_env 0 (V::nil)) (Q := subst_env 0 (V::nil) N'').
    intros.
    apply subst_env_compat_rw; auto.
   auto.
  auto.
 (* The following strange pattern puts the goal in a form where
    SN_double_induction can apply. It effectively generalizes the
    goal, so that we prove it not just for N'' and P, but for
    "anything downstream of" the respective terms. *)
 double_induction_SN_intro P N''.
 subst N''.

 assert (Typing nil P' S) by (eauto with Reducible).
 assert (Reducible P' S) by (eauto with Reducible).
 apply Neutral_Reducible_withdraw; [sauto | seauto |].
 intros M' redn.

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | | | | | | | | | | | | | | | | | |].

 (* Case: beta reduction. *)
   subst V M0 N0.
   replace (shift 0 1 P') with P' in M'_eq by (symmetry; eauto with Shift).
   simpl in M'_eq.
   replace (unshift 0 1 (subst_env 0 (P' :: nil) N'''))
      with (subst_env 0 (P' :: nil) N''') in M'_eq.

    rewrite M'_eq.
    assert (subst_env 0 (P' :: Vs) N ~>> subst_env 0 (P' :: nil) N''').
     replace (subst_env 0 (P'::Vs) N)
        with (subst_env 0 (P'::nil) (subst_env 1 Vs N)).
      auto.
     eapply subst_env_concat; simpl; solve [eauto with Term].
    assert (Reducible (subst_env 0 (P'::Vs) N) T) by auto.
    solve [eauto with Reducible].
   (* To show that unshift 0 1 has no effect on (subst_env 0 [P'] N'''). *)
   (* First, N, after substitution of P'::Vs, is closed: *)
   assert (Typing nil (subst_env 0 (P'::Vs) N) T).
    apply subst_env_preserves_typing with (S::Ts); solve [auto with Term].
   (* Next, N''', after substitution of [P'], is closed: *)
   assert (Typing nil (subst_env 0 (P'::nil) N''') T).
    assert (Typing nil (subst_env 0 (P'::nil) (subst_env 1 Vs N)) T).
     erewrite subst_env_concat; simpl; solve [eauto with Term].
     (* Rw_rt_preserves_types is automatic *)
    eapply Rw_rt_preserves_types; solve [eauto].
   symmetry; apply unshift_closed_noop with T; solve [auto].
 (* Case: Reduction in left subterm. *)
  inversion L_redn.
  subst n m1 m2 n0.
  apply IHN''; solve [eauto].
 (* Case: Reduction in right subterm. *)
 apply IHP; solve [eauto].
Qed.

Lemma pair_proj_reducible:
  forall (M N : Term)
         (S T : Ty)
         (b : bool),
  Reducible M S ->
  Reducible N T ->
  SN M ->
  SN N ->
     Reducible (TmProj b (〈M, N〉)) (if b then T else S).
Proof.
 intros.
 double_induction_SN N M.
 intros x y X1 X2 H1 H2.

 apply Neutral_Reducible_withdraw; auto.
 (* Discharge the typing obligation. *)
 - assert (Typing nil y T) by solve [eauto with Reducible].
   assert (Typing nil x S) by solve [eauto with Reducible].
   destruct b; eauto.
 (* All reducts are reducible. *)
 - intros M' H3.
   (* Take cases on the reduction. *)
   inversion H3 as [ | | | | | | m n1 n2 H7 | m n | m n | | | | | | | | | | | | | | | |]; subst.
   (* Case: reduction under the operation. *)
   * inversion H7; subst; eauto.
   (* Case: beta-reduction on the left *)
   * eauto with Reducible.
   (* Case: beta-reduction on the right *)
   * eauto with Reducible.
Qed.

(** (Lemma 29, for pairs rather than records) *)
Lemma pair_reducible:
  forall M N S T,
    Reducible M S -> Reducible N T -> Reducible (TmPair M N) (TyPair S T).
Proof.
 intros.
 simpl.
 assert (Typing nil M S) by solve [auto with Reducible].
 assert (Typing nil N T) by solve [auto with Reducible].
 assert (SN M) by (eapply Reducible_SN; eauto).
 assert (SN N) by (eapply Reducible_SN; eauto).
 intuition.
 (* Case TmProj false *)
 - apply (pair_proj_reducible M N S T false X X0 H1 H2).
 (* Case TmProj true *)
 - apply (pair_proj_reducible M N S T true X X0 H1 H2).
Qed.

(** * Reducible things at list type *)

Lemma ReducibleK_Empty :
  forall T, ReducibleK Reducible nil T.
Proof.
 unfold ReducibleK.
 simpl.
 intros.
 eauto using SN_TmSingle with SN.
Qed.

(* Hint Resolve ReducibleK_Empty. *)

(** (compare Lemma 26, but not the same) *)
Lemma Reducible_Null:
  forall K T,
    ReducibleK Reducible K T
    -> SN (plug TmNull K).
Proof.
 unfold ReducibleK.
 intros.
 assert (Krw_rt K K).
  apply Krw_rt_refl; sauto.
 revert H.
 pattern K at 2 3.
 apply Ksize_induction with (K := K); intros; auto.
  destruct K0; simpl in *; try (inversion H).
  apply reducts_SN.
  intros m' H'.
  inversion H'.
 destruct K'.
 inversion H0.
 destruct (Reducible_inhabited T) as [M M_H].
 pose (X M M_H).
 apply SN_K_M_SN_K_Null with (TmSingle M).
 apply Rw_trans_preserves_SN with (plug (TmSingle M) K); auto.
 apply Krw_rt_Rw_rt; auto.
Qed.

(** (Lemma 32; compare Lemmas 30, 31. It seemed a lot harder) *)
Lemma Reducible_Union:
  forall T M N,
    Reducible M (TyList T) -> Reducible N (TyList T) -> Reducible (TmUnion M N) (TyList T).
Proof.
 simpl.
 intros T M N.
 intros.
 destruct X, X0.
 split.
  auto.
 intros.
 change (forall K, ReducibleK Reducible K T -> SN (plug M K)) in s.
 change (forall K, ReducibleK Reducible K T -> SN (plug N K)) in s0.
 change (ReducibleK Reducible K T) in X.
 eauto using SN_K_Union.
Qed.

(** * Rewrites Inside Structures That Look Like A Beta-Reduct. *)

(** When the result of a substitution is SN, the original
    unsubstituted term is, too. (Compare Lemma 44) *)
Lemma SN_less_substituent:
  forall L N,
    SN (N */ L) ->
    SN N.
Proof.
 intros.
 apply SN_embedding with (f := fun x => x */ L) (Q := N */ L); auto.
 intros.
 apply unshift_substitution_preserves_rw; sauto.
Qed.

Lemma beta_reduct_under_K_rw_rt:
  forall K K0, Krw_rt K K0 ->
  forall N N0, (N ~>> N0) ->
  forall L L0, (L ~>> L0) ->
    plug (N */ L) K ~>>
    plug (N0 */ L0) K0.
Proof.
 intros.
 assert ((N */ L) ~>> (N0 */ L0)).
 apply unshift_substitution_doubly_preserves_rw_rt; auto.
 apply plug_rw_rt; auto.
Qed.

(** * Bind reducibility. (Lemma 33) *)

Lemma K_TmTable_rw:
  forall K t M,
    (plug (TmTable t) K ~> M) ->
    {K' : Continuation & M = plug (TmTable t) K' & Krw K K'} +
    {K' : Continuation
          & (TmNull, K') = deepest_K M (* how about just M = plug K' TmNull ? *)
          & {K'' : Continuation & K = appendK K'' (Iterate TmNull :: K')}}.
Proof.
  induction K using Ksize_induction_strong.
  intros.
  apply three_ways_to_reduce_at_interface in H0.
  destruct H0 as [[[[[K'' Zeq rw]| [K'' Zeq rw]]| p] | [K'' Zeq  [K0 K''eq]]]| ?].
  - inversion rw.
  - left; eauto.
  - destruct p.
    lapply n; easy.
  - subst.
    right.
    exists K''.
    * rewrite deepest_K_TmNull; auto.
    * exists K0.
      auto.
  - destruct s as [L' [M' eq]].
    inversion eq.
Qed.

(* TODO: see if you can replace all uses of K_TmTable_rw with this version. *)
Lemma K_TmTable_rw2:
  forall K t M,
    (plug (TmTable t) K ~> M) ->
    {K' : Continuation & M = plug (TmTable t) K' & Krw K K'} +
    {K' : Continuation
          & M = plug TmNull K'
          & {K'' : Continuation & K = appendK K'' (Iterate TmNull :: K')}}.
Proof.
  induction K using Ksize_induction_strong.
  intros.
  apply three_ways_to_reduce_at_interface in H0.
  destruct H0 as [[[[[K'' Zeq rw]| [K'' Zeq rw]]| p] | [K'' Zeq  [K0 K''eq]]]| ?].
  - inversion rw.
  - left; eauto.
  - destruct p.
    lapply n; easy.
  - subst.
    right.
    exists K''.
    * auto.
    * exists K0.
      auto.
  - destruct s as [L' [M' eq]].
    inversion eq.
Qed.

Lemma Rw_over_TmTable_generalizes:
  forall t x K K',
    (plug (TmTable t) K ~> plug (TmTable t) K') ->
    (plug x K ~> plug x K').
Proof.
 intros.
 apply K_TmTable_rw in H.
 destruct H as [? | ?].
 - destruct s as [? H H0].
   unfold Krw in H0.
   assert (deepest_K (TmTable t) = (TmTable t, nil)).
   auto.
   pose (deepest_K_TmTable K' t).
   pose (deepest_K_TmTable x0 t).
   assert (x0 = K').
   congruence.
   subst x0.
   auto.
 - destruct s as [? H H0].
   assert (deepest_K (plug (TmTable t) K') = (TmTable t, K')).
   replace K' with (appendK nil K') at 2 by auto.
   apply deepest_K_plug.
   trivial.
   rewrite H1 in H.
   congruence.
Qed.

Lemma discriminate_K_TmTable_K_TmNull:
  forall K t K', ~(plug (TmTable t) K = plug TmNull K').
Proof.
  intros.
  intro.
  assert (deepest_K (plug (TmTable t) K) = deepest_K (plug TmNull K')).
  {f_equal. auto. }
  rewrite deepest_K_TmNull in H0.
  rewrite deepest_K_TmTable in H0.
  discriminate.
Qed.

Lemma deepest_K_NotBind:
  forall K M K' M',
    NotBind M -> NotBind M' ->
    (M', K') = deepest_K (plug M K) ->
    (M', K') = (M, K).
Proof.
Admitted.

(* To do: Generalize this lemma:

  deepest_K_NotBind:
    forall (K : Continuation) (M : Term) (K' : Continuation) (M' : Term),
    (K', M') = deepest_K (plug K M) -> NotBind M -> M = M'

  the next lemma and a couple others would fall out.
*)
Lemma plug_TmTable_unique: forall K K' t,
    plug (TmTable t) K = plug (TmTable t) K'
    -> K = K'.
Proof.
  intros.
  assert (deepest_K (plug (TmTable t) K) = deepest_K (plug (TmTable t) K')).
  f_equal; auto.
  rewrite deepest_K_TmTable in H0.
  rewrite deepest_K_TmTable in H0.
  congruence.
Qed.

(** This is kind of gross, but it's a means to an end. One lemma seemed
    particularly hard to prove by induction on the RewritesTo_rt type, because
    of the _trans case. It was much easier using this equivalent data
    structure, which is a right-linear linked-list of reduction steps. Perhaps
    I should have done all reduction sequences this way from the beginning? *)

Inductive RewritesTo_rt_right_linear : Term -> Term -> Type :=
  Rw_rt_rl_null : forall m n, m = n -> RewritesTo_rt_right_linear m n
| Rw_rt_rl_cons : forall l m n, (l ~> m) ->
                  RewritesTo_rt_right_linear m n ->
                  RewritesTo_rt_right_linear l n.

#[local] Hint Constructors RewritesTo_rt_right_linear : flatten_rw.

Lemma concat_redseq:
  forall l m n
         (r0 : RewritesTo_rt_right_linear l m)
         (r1 : RewritesTo_rt_right_linear m n),
    RewritesTo_rt_right_linear l n.
Proof.
  intros l m n r0. induction r0; intros; subst.
  auto.
  eapply Rw_rt_rl_cons; eauto.
Qed.

Lemma normal_redseq:
  forall l m (r:l ~>> m), RewritesTo_rt_right_linear l m.
Proof.
 intros.
 induction r; intros; subst.
 - auto with flatten_rw.
 - eauto with flatten_rw.
 - eauto using concat_redseq.
Qed.

Lemma return_redseq:
  forall l m, (RewritesTo_rt_right_linear l m) -> (l ~>> m).
Proof.
  intros l m H.
  induction H; eauto.
Qed.

Lemma once_TmNull_subject_always:
  forall A Z,
    (A ~>> Z) -> {K & A = plug TmNull K}
    -> {K' & deepest_K Z = (TmNull, K')}.
Proof.
  intros.
  induction H; intros; destruct H0 as [K H0]; subst.
  - exists K.
    apply deepest_K_TmNull.
  - apply K_TmNull_rw in r.
    destruct r as [[K' neq [K'' size Keq]] | ].
    exists K'.
    subst.
    apply deepest_K_TmNull.
    destruct s.
    exists x.
    subst.
    apply deepest_K_TmNull.
  - firstorder.
    specialize (H2 K).
    firstorder.
    specialize (H0 x).
    simpl in H0.
    symmetry in p.
    apply deepest_K_spec in p.
    auto.
Qed.

Lemma Rw_rt1_intermediate_TmTable_subject':
  forall t Z m,
    (RewritesTo_rt_right_linear m Z) -> {K' & Z = plug (TmTable t) K'} ->
    forall A,
    (A ~> m) -> {K & A = plug (TmTable t) K} ->
    {K'' & m = plug (TmTable t) K''}.
Proof.
  intros t Z m H.
  induction H; intros; subst.
  - eauto.
  - firstorder.
    subst.
    apply K_TmTable_rw in H1.
    destruct H1 as [[K' leq] | [K' leq [K'' xeq]]].
    * exists K'; auto.
    * assert (l = plug TmNull K' ).
      { symmetry.
        apply deepest_K_spec.
        auto. }
      assert (H5: l ~>> plug (TmTable t) x0).
      { pose (return_redseq _ _ H).
        eauto. }
      lapply (once_TmNull_subject_always l (plug (TmTable t) x0) H5).
      { intro H6.
        destruct H6.
        rewrite deepest_K_TmTable in e.
        easy. }
      eauto.
Qed.

Lemma Rw_rt1_intermediate_TmTable_subject:
  forall t Z m,
    (m ~>> Z) -> {K' & Z = plug (TmTable t) K'} ->
    forall A,
    (A ~> m) -> {K & A = plug (TmTable t) K} ->
    {K'' & m = plug (TmTable t) K''}.
Proof.
 intros.
 pose (normal_redseq _ _ H).
 eapply Rw_rt1_intermediate_TmTable_subject'; eauto.
Qed.

Lemma Rw_rt_intermediate_TmTable_subject:
  forall t A Z m,
    (A ~>> m) -> {K & A = plug (TmTable t) K} ->
    (m ~>> Z) -> {K' & Z = plug (TmTable t) K'} ->
    {K'' & m = plug (TmTable t) K''}.
Proof.
  intros.
  induction H; intros; subst.
  - eauto.
  - destruct H0; destruct H2.
    subst.
    eauto using Rw_rt1_intermediate_TmTable_subject.
  - firstorder.
    subst.
    assert (cmon: plug (TmTable t) x0 = plug (TmTable t) x0) by reflexivity.
    assert (m ~>> plug (TmTable t) x).
    eauto.
    destruct (H2 x0 cmon H4).
    apply H0 with x1; auto.
Qed.

Lemma Rw_rt_over_TmTable_generalizes:
  forall t x K K',
    (plug (TmTable t) K ~>> plug (TmTable t) K')
    -> (plug x K ~>> plug x K').
Proof.
  intros t x K K' H.
  remember (plug (TmTable t) K) as A.
  remember (plug (TmTable t) K') as Z.
  revert K HeqA K' HeqZ.
  induction H; intros; subst.
  - assert (K = K') by (eauto using plug_TmTable_unique).
    subst; auto.

  - eauto using Rw_over_TmTable_generalizes.

  - assert (H1 : {K'' & m = plug (TmTable t) K''}).
    { eauto using Rw_rt_intermediate_TmTable_subject. }
    destruct H1.

    eapply Rw_rt_trans.
    * apply IHRewritesTo_rt1; eauto.
    * apply IHRewritesTo_rt2; auto.
Qed.

(* TODO: Seems like this is overly long.
   I wonder if the induction on K is needed?
 *)
Lemma bind_sn_withdraw:
  forall K L N,
    SN L ->
    SN (plug (N */ L) K) ->
    SN (plug (TmBind (TmSingle L) N) K).
Proof.
  induction K using Ksize_induction_strong.
  rename H into IHK.
  intros L N H H0.
  assert (SN N).
   apply SN_push_under_k in H0.
   eauto using SN_less_substituent.
  apply triple_induction_scoped with (K0:=K) (M0:=N) (N0:=L);
    eauto using Krw_norm_from_SN.
  intros K0 N0 L0 ? ? ? IHK0 IHM0 IHL0.
  apply reducts_SN; fold SN.
  intros Z redn.
  apply three_ways_to_reduce_at_interface in redn
    as [[[[[M' redn_a redn_b] | [K'' redn_a redn_b]] | ?] | ?] | ?].
  * (* Inside body. *)
    inversion redn_b; subst.
    -- (* Bind_Null_body *) eauto using beta_reduct_under_K_rw_rt, Rw_trans_preserves_SN.
    -- (* beta *)
       assert (SN (plug (N */ L) K0)).
       apply Krw_rt_preserves_SN with K; auto.
       apply plug_SN_rw_rt with (N */ L); auto.
       apply unshift_substitution_doubly_preserves_rw_rt; auto.
    -- (* TmBind_union_body *) admit.
    -- (* subject reduces *) inversion H8; sauto.
    -- (* body reduces *) seauto.
  * (* Inside continuation. *)
    subst.
    auto.
  * (* At the interface, and body is not a Bind term. *)
    refute.
    destruct p as [A [K' [M' H6 [N' H7 H8]]]].
    apply NotBind_TmBind in H8; auto.
  * destruct s as [K' Zeq [K'' K0eq]].
    assert (plug (N */ L) K ~>> plug TmNull K').
    apply Rw_rt_trans with (plug (N */ L) K0).
    apply plug_rw_rt; auto.
    subst.
    apply Rw_rt_step.
    apply curtailment.
    subst.
    eauto using plug_SN_rw_rt.
  * (* The the interface, and body is a Bind term. *)
    destruct s as [L1 [L1' H8 [K'' [N1 H9 H10]]]].
    inversion H8.
    subst Z L1 L1' K0.
    apply IHK.
    { apply Krw_rt_conserves_Ksize in H2.
      simpl in H2.
      lia. }
    { eauto. }
    assert (SN (plug (unshift 0 1 (subst_env 0 (shift 0 1 L0 :: nil) N0)) (Iterate N1 :: K''))).
     assert (plug (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)) K
                ~>> plug (unshift 0 1 (subst_env 0 (shift 0 1 L0 :: nil) N0)) (Iterate N1 :: K'')).
      apply beta_reduct_under_K_rw_rt; sauto.
     apply Rw_trans_preserves_SN in H5; sauto.
    simpl in H5 |- *.

    replace (unshift 1 1 (subst_env 1 (shift 0 1 (shift 0 1 L0) :: nil)
                                    (shift 1 1 N1)))
      with N1.
    { auto. }
    rewrite subst_unused_noop.
    symmetry; apply unshift_shift.
    pose (shift_freevars_range N1 1).
    unfold in_env_domain.
    simpl in a |- *.
    eapply all_cut; [| apply a]; simpl.
    intros; lia.
Unshelve.
Admitted.

Lemma Bind_Reducible_core:
  forall (M : Term) (S : Ty) (N : Term) (T : Ty),
    Typing (S :: nil) N (TyList T) ->
    Reducible M (TyList S) ->
    SN M ->
    SN N ->
    forall K : Continuation,
      ReducibleK Reducible K T ->
      (forall L : Term, Reducible L S ->
                        SN (plug (N */ L) K)) ->
      SN (plug (TmBind M N) K).
Proof.
 intros.
 enough (SN (plug M (Iterate N :: K))) by auto.
 simpl in X.
 apply X.
 simpl.
 intros.
 apply bind_sn_withdraw.
 { eauto using Reducible_SN. }
 auto.
Qed.

(** (Lemma 34) *)
Lemma Bind_Reducible :
  forall M S N T,
    Typing (S :: nil) N (TyList T)
    -> Reducible M (TyList S)
    -> (forall L, Reducible L S
                  -> Reducible (N */ L) (TyList T))
    -> Reducible (TmBind M N) (TyList T).
Proof.
 intros.
 split.
  intuition; solve [eauto with Reducible].
 intros.
 simpl in X0.
 assert (forall L, Reducible L S -> SN (plug (N */ L) K)).
 intros.
  apply X0; auto.
 assert (SN M).
 eapply Reducible_SN; eauto.
 assert (SN N).
  destruct (Reducible_inhabited S) as [L L_red].
  specialize (X0 L L_red).
  destruct X0 as [t s].
  specialize (s nil).
  lapply s.
   simpl.
   apply SN_less_substituent.
  apply ReducibleK_Empty.
 clear X0.
 eapply Bind_Reducible_core; eauto.
Qed.

Lemma TmTable_rw:
  forall K t x,
    (plug (TmTable t) K ~> x) ->
    {K' : Continuation & (x = plug (TmTable t) K') & Krw K K'} +
    {K' : Continuation & prefix K' K & x = plug TmNull K'}.
Proof.
  (* induction K; simpl; intros. *)
  (* inversion H. *)
  simpl; intros.
  apply three_ways_to_reduce_at_interface in H.
  destruct H as [[[[[M' H H1] | H] | H] | H] | ?].
  - inversion H1.
  - eauto.
  - destruct H.
    lapply n.
    tauto.
    auto.
  - destruct H as [K' xeq [K'' Keq]].
    subst.
    right.
    exists K'; auto.
    apply prefix_appendK.
    auto.
  - firstorder.
    discriminate.
Qed.

Lemma Rw_curtailment_generalizes: forall K t K',
    (plug (TmTable t) K ~> plug TmNull K') ->
    forall x, plug x K ~> plug TmNull K'.
Proof.
  intros.
  apply K_TmTable_rw in H.
  destruct H as [[K0 H H0] | [K0 H H0]].
  - symmetry in H; apply discriminate_K_TmTable_K_TmNull in H.
    easy.
  - destruct H0.
    assert (K' = K0).
    rewrite deepest_K_TmNull in H.
    congruence.
    subst.
    apply curtailment.
Qed.

(* TODO: Ugly. Unify all the SN_embedding lemmas--or name them well. *)
Lemma SN_embedding2'' A f g:
    forall M : A,
    (forall (N : A) (Z : Term),
        (g M ~>> g N) ->
        (g N ~> Z) ->
        ({M' : A & ((Z = g M') *
                    (f N ~> f M'))%type}
         + SN Z)) ->
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

Lemma SN_K_TmTable:
  forall t K x,
    SN (plug x K) -> SN (plug (TmTable t) K).
Proof.
  induction K using Ksize_induction_strong.
  intros.
  apply SN_embedding2'' with (f:=fun k => plug x k)
                            (g:=fun k => plug (TmTable t) k);
    auto.
  intros K' Z Hdown H1.
  clone H1.
  apply K_TmTable_rw2 in H1.
  destruct H1 as [[K'' Zeq rw] | [K'' eq [K''' K'''eq]]].
  - left.
    exists K''.
    intuition.
  - right.
    subst Z.
    apply SN_K_M_SN_K_Null with (TmTable t).
    assert (Ksize K'' < Ksize K).
    { assert (Ksize K' <= Ksize K).
      { apply Rw_rt_conserves_Ksize.
        trivial.
        eauto using Rw_rt_over_TmTable_generalizes. }
      assert (Ksize K' > Ksize K'').
      { subst K'.
        rewrite Ksize_appendK; simpl.
        lia. }
      lia. }
    apply H with TmNull; auto.
    apply Rw_trans_preserves_SN with (plug x K); auto.
    assert (plug x K' ~> plug TmNull K'').
    apply Rw_curtailment_generalizes with t; auto.
    assert (plug x K ~>> plug x K').
    { eauto using Rw_rt_over_TmTable_generalizes. }
    eauto.
Qed.

(** Every well-typed term, with a [Reducible] environment that makes it a closed
    term, is [Reducible] at its given type. *)
Theorem reducibility:
  forall M T tyEnv Vs,
    Typing tyEnv M T ->
    env_typing Vs tyEnv ->
    env_Reducible Vs tyEnv ->
    Reducible (subst_env 0 Vs M) T.
Proof.
 induction M; simpl; intros T tyEnv Vs tp Vs_tp Vs_red;
   inversion tp; inversion Vs_tp.
 (* Case TmConst *)
 * simpl.
   intuition.

 (* Case TmVar *)
 * replace (x - 0) with x by lia.
   case_eq (nth_error Vs x); [intros V V_H | intro H_bogus].
    eapply Reducible_env_value; eauto.
   absurd (length Vs <= x).
    cut (length tyEnv > x); [lia|]. (* todo: sufficient ... by lia. *)
    seauto.
   apply <- nth_error_overflow; sauto.

 (* Case TmPair *)
 * assert (Reducible (subst_env 0 Vs M2) t) by eauto.
   assert (Reducible (subst_env 0 Vs M1) s) by eauto.
   simpl.
   assert (Reducible (TmPair (subst_env 0 Vs M1) (subst_env 0 Vs M2)) (TyPair s t)).
    apply pair_reducible; sauto.
   simpl in X1.
   trivial.

 (* Case TmProj false *)
 * subst.
   rename M into M, T into S, t into T.
   assert (x0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
    seauto.
   simpl in x0.
   tauto.

 (* Case TmProj true *)
 * subst.
   rename M into M, s into S.
   assert (X0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
    seauto.
   simpl in X0.
   tauto.

 (* Case TmAbs *)
 * (* TODO: Should be a simpler way to autorewrite this *)
   replace (map (shift 0 1) Vs) with Vs by (symmetry; eauto with Shift).
   replace (TmAbs (subst_env 1 Vs M)) with (subst_env 0 Vs (TmAbs M)).
   (* proof of reducibility of the lambda. *)
   - apply lambda_reducibility with tyEnv; auto.
     intros V V_red.
     eapply IHM; eauto with Reducible Term.
     simpl.
     intuition.

   (* Obligation: TmAbs (subst_env 1 Vs m) = subst_env 0 Vs (TmAbs m). *)
   - simpl.
     erewrite env_typing_shift_noop; eauto.

 (* Case TmApp *)
 * subst.
   assert (Reducible (subst_env 0 Vs M1) (TyArr a T)) by eauto.
   assert (Reducible (subst_env 0 Vs M2) a) by eauto with Reducible.
   inversion X.
   apply X1.
   apply Reducible_welltyped_closed.
   auto.
   apply X0.

 (* Case TmNull *)
 * simpl.
   split.
   { auto. }
   intro K.
   apply Reducible_Null.

 (* Case TmSingle *)
 * simpl.
   split.
   { eauto. }
   intros.
   eauto.

 (* Case TmUnion *)
 * subst.
   assert (Reducible (subst_env 0 Vs M2) (TyList t)) by eauto.
   assert (Reducible (subst_env 0 Vs M1) (TyList t)) by eauto.
   apply Reducible_Union; sauto.

 (* Case TmBind *)
 * subst.
   apply Bind_Reducible with s.
   (* Typing *)
   - eapply subst_env_preserves_typing with (env' := tyEnv); auto.
     rewrite env_typing_shift_noop with (env := tyEnv); auto.
   (* Precondition: that M1 is Reducible. *)
   - eapply IHM1; eauto.

   (* Precondition: that M2 is Reducible, for any substitution with Reducible L. *)
   - clear H1 IHM1 M1 tp.

     intros.
     pose (Reducible_welltyped_closed _ _ X).
     assert (Typing nil (subst_env 0 (L :: Vs) M2) (TyList t)).
     { eapply closing_subst_closes; eauto with Term. }

     erewrite shift_closed_noop; eauto.
     erewrite shift_closed_noop_map; eauto.
     rewrite subst_env_concat with (env := s :: tyEnv).
     (* TO DO: The env_typing oblig. of subst_env_concat seems unnecessary. *)
     ** unfold app.
        erewrite unshift_closed_noop (* with (T:=TyList t) *); eauto.
        eapply IHM2; eauto with Term.
        simpl.
        auto.
     ** apply env_typing_cons; sauto.
 * simpl.
   split.
   { eauto. }
   intros.
   destruct (Reducible_inhabited t).
   eapply SN_K_TmTable; eauto.
Qed.

(** Every well-typed term is strongly normalizing. *)
Lemma normalization :
  forall M T,
    Typing nil M T ->
    SN M.
Proof.
 intros M T tp.

 assert (Reducible M T).
  replace M with (subst_env 0 nil M) by solve [eauto with Subst].
  eapply reducibility; eauto; solve [firstorder].
 (* With reducibility comes strong normalization. *)
 solve [eauto with SN].
Qed.

(** Prints out "Closed under the global context" if we have no
remaining assumptions. *)
Print Assumptions normalization.
