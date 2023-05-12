(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Load "eztactics.v".

Add LoadPath "Listkit" as Listkit.

Require Import Arith.
Require Import Lia.
Require Import List.

Require Import Listkit.AllType.
Require Import Listkit.Foreach.
Require Import Listkit.NthError.
Require Import Listkit.Sets.
Require Import Listkit.listkit.
Require Import Listkit.logickit.

(* Add LoadPath ".". *)

Require Import Continuation.
Require Import Knorm.
Require Import Monomorphism.
Require Import Norm.
Require Import OutsideRange.
Require Import Rewrites.
Require Import Shift.
Require Import Subst.
Require Import Term.
Require Import Typing.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Import Setoid.
Require Import Coq.Program.Basics. (* TODO: What's this for?? *)
Require Import Bool.

(* Set Loose Hint Behavior Strict. *)

#[export]
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
  eauto with Norm.
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
  (* | TyPair s t =>
    Reducible (TmProj false tm) s * Reducible (TmProj true tm) t *)
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
   inversion b; solve [auto with Norm].
 - firstorder using Rw_preserves_types.
 (* - firstorder using Rw_preserves_types. *)
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
 auto with Norm.
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
      simpl; solve [eauto with Norm].
    (* Reducible -> SN *)
     simpl.
     tauto.
    (* Neutral terms withdraw *)
    unfold Reducible in *.
    intuition (apply reducts_SN).
    solve [firstorder].

  (* Case TyArr *)
  splitN 3.
  (* Exists a reducible term at T1->T2 *)
    destruct IHT2 as [[[N N_Red] Red_T2_tms_SN] IHT2_Red_neutral_withdraw].
    (* Given any term at T2, we can abstract it with a dummy argument. *)
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
    inversion red as [ | ? Z ? redn_Z | | | | | | | ] ; subst.
    (* beta reduction *)
      rewrite subst_dummyvar_beta.
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
   firstorder.
   auto using TSingle.
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
 clone H3 as H2.
 apply Neutral_Lists in H3 as [
  (* [ *)
    [M' s1 s2]
     | [K1 s1 s2]]
      (* | [K' eq [K'' xeq]]] *)
      ; [ | | auto ].
 - subst.
   firstorder.
 - subst.
   apply X1; auto.
   rename x into K.
   apply Krw_preserves_ReducibleK with K; auto.
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

Lemma SN_one_fewer_subst:
  forall (N : Term) (S T : Ty) (Ts : list Ty) (Vs : list Term)
         (N_tp : Typing (S :: Ts) N T)
         (Vs_tp: env_typing Vs Ts) (Vs_red: env_Reducible Vs Ts)
         (H: forall V : Term, Reducible V S -> Reducible (subst_env 0 (V :: Vs) N) T),
    SN (subst_env 1 Vs N).
Proof.
  intros.
  destruct (Reducible_inhabited S) as [V V_Red].
  assert (SN (subst_env 0 (V :: Vs) N)).
  { eauto using Reducible_SN, H. }
  apply SN_embedding with (f:=subst_env 0 (V :: nil)) (Q:=subst_env 0 (V::Vs) N); auto.
  - auto using subst_env_compat_rw.
  - rewrite subst_env_concat with (env := S::Ts); auto.
    apply env_typing_cons; auto.
    apply Reducible_welltyped_closed; auto.
Qed.

Lemma Reducible_beta_1:
  forall N P S T,
    Typing (S::nil) N T ->
    (forall V : Term, Reducible V S -> Reducible (subst_env 0 (V::nil) N) T) ->
    Reducible P S ->
    Reducible (N */ P) T.
Proof.
  intros.
  assert (Typing nil P S).
  auto with Reducible.
  erewrite closed_beta_subst; eauto.
Qed.

Lemma Reducible_beta_1_many:
  forall N P Vs Ts S T,
    Typing (S::Ts) N T ->
    env_typing Vs Ts ->
    (forall V : Term, Reducible V S -> Reducible (subst_env 0 (V :: Vs) N) T) ->
    Reducible P S ->
    Reducible (subst_env 1 Vs N */ P) T.
Proof.
  intros.
  apply Reducible_beta_1 with (S := S).
  - eapply subst_env_preserves_typing; eauto.
  - intros.
    erewrite subst_env_concat; simpl; eauto.
    * apply Reducible_welltyped_closed in X1.
      apply env_typing_cons; eauto.
  - auto.
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
 { eapply subst_env_preserves_typing; eauto. }

 (* Reducibility *)
 intros P P_tp P_red.

 simpl.
 erewrite shift_closed_noop_map; eauto.

 assert (SN P) by eauto with SN.
 set (N'' := subst_env 1 Vs N).
 assert (SN_N'' : SN N'').
 { eauto using SN_one_fewer_subst. }

 (* The following strange pattern puts the goal in a form where
    SN_double_induction can apply. It effectively generalizes the
    goal, so that we prove it not just for N'' and P, but for
    "anything downstream of" the respective terms. *)
 double_induction_SN_intro P N''.

 assert (Typing nil P' S) by (eauto with Reducible).
 assert (Reducible P' S) by (eauto with Reducible).
 apply Neutral_Reducible_withdraw; [ sauto | eauto with Subst |].
 intros M' redn.

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | |].

 - (* Case: beta reduction. *)
   subst N''.
   subst.
   apply Rw_rt_preserves_Reducible with (subst_env 1 Vs N */ P').
   eapply Reducible_beta_1_many; eauto.
   apply beta_substitution_doubly_preserves_rw_rt; auto.
 - (* Case: Reduction in left subterm. *)
   inversion L_redn.
   subst n m1 m2 n0.
   apply IHN''; solve [eauto].
 - (* Case: Reduction in right subterm. *)
   apply IHP; solve [eauto].
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
 apply beta_substitution_preserves_rw; sauto.
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
 apply beta_substitution_doubly_preserves_rw_rt; auto.
 apply plug_rw_rt; auto.
Qed.

(** * Bind reducibility. (Lemma 33) *)

(** This is kind of gross, but it's a means to an end. One lemma seemed
    particularly hard to prove by induction on the RewritesTo_rt type, because
    of the trans case. It was much easier using this equivalent data
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
    (A ~>> Z) -> {K & A = plug (TmVar 0) K}
    -> {K' & deepest_K Z = ((TmVar 0), K')}.
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

Lemma assoc_result_SN:
  forall (K : Continuation) (L N : Term) (N0 L0 : Term) (K'' : Continuation) (N1 : Term),
    SN (plug (N */ L) K) ->
    Krw_rt K (Iterate N1 :: K'') ->
    (N ~>> N0) -> (L ~>> L0) ->
    SN (plug (TmBind N0 (shift 1 1 N1) */ L0) K'').
Proof.
  intros.
  simpl.
  rewrite beta_assoc_simpl.
  eapply Rw_trans_preserves_SN; eauto.
  assert (H5:plug (N */ L) K ~>> plug (N0 */ L0) (Iterate N1 :: K'')).
  { apply beta_reduct_under_K_rw_rt; sauto. }
  simpl in *.
  auto.
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
  { apply SN_push_under_k in H0.
    eauto using SN_less_substituent. }
  apply triple_induction_scoped with (K0:=K) (M0:=N) (N0:=L);
    eauto using Krw_norm_from_SN.
  intros K0 N0 L0 ? ? ? IHK0 IHM0 IHL0.
  apply reducts_SN; fold SN.
  intros Z redn.
  apply interface_rw_classification in redn
    as [
      (* [ *)
        [
          [
            [M' redn_a redn_b]
             | [K'' redn_a redn_b]]
              | ?]
               (* | ?] *)
                | ?].
  * (* Inside body. *)
    inversion redn_b; subst.
    -- (* Bind_Null_body *) eauto using beta_reduct_under_K_rw_rt, Rw_trans_preserves_SN.
    (* -- (* beta *)
       assert (SN (plug (N */ L) K0)).
       apply Krw_rt_preserves_SN with K; auto.
       apply plug_SN_rw_rt with (N */ L); auto.
       apply beta_substitution_doubly_preserves_rw_rt; auto. *)
    -- (* subject reduces *) inversion H8; sauto.
    -- (* body reduces *) seauto.
  * (* Inside continuation. *)
    subst.
    auto.
  * (* At the interface, and body is not a Bind term. *)
    refute.
    destruct p as [A [K' [M' H6 [N' H7 H8]]]].
    apply NotBind_TmBind in H8; auto.
   * (* At the interface, and body is a Bind term. *)
    destruct s as [L1 [L1' H8 [K'' [N1 H9 H10]]]].
    inversion H8.
    subst Z L1 L1' K0.
    apply IHK.
    { apply Krw_rt_conserves_Ksize in H2.
      simpl in H2.
      lia. }
    { eauto with Norm. }
    eauto using assoc_result_SN.
Qed.

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
  specialize (X2 L L_red).
  apply SN_push_under_k in X2.
  eauto using SN_less_substituent.
 clear X0.
 eapply Bind_Reducible_core; eauto.
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
    enough (length tyEnv > x) by lia.
    solve [eauto with NthError].
   apply <- nth_error_overflow; sauto.

 (* Case TmAbs *)
 * (* TODO: Should be a simpler way to autorewrite this *)
   erewrite shift_closed_noop_map; eauto.
   replace (TmAbs (subst_env 1 Vs M)) with (subst_env 0 Vs (TmAbs M)).
   (* proof of reducibility of the lambda. *)
   - apply lambda_reducibility with tyEnv; auto.
     intros V V_red.
     eapply IHM; eauto with Reducible Term.
     simpl.
     intuition.

   (* Obligation: TmAbs (subst_env 1 Vs m) = subst_env 0 Vs (TmAbs m). *)
   - simpl.
     erewrite shift_closed_noop_map; eauto.

 (* Case TmApp *)
 * subst.
   assert (Reducible (subst_env 0 Vs M1) (TyArr a T)) by eauto.
   assert (Reducible (subst_env 0 Vs M2) a) by eauto with Reducible.
   inversion X.
   apply X1.
   apply Reducible_welltyped_closed.
   auto.
   auto.

(* Case TmSingle *)
  * simpl.
  split.
  { eauto with Subst. }
  intros.
  eauto.

 (* Case TmBind *)
 * subst.
   apply Bind_Reducible with s.
   (* Typing *)
   - eapply subst_env_preserves_typing with (env' := tyEnv); auto.
     erewrite shift_closed_noop_map; eauto.
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
        erewrite unshift_closed_noop; eauto.
        eapply IHM2; eauto with Term.
        simpl.
        auto.
     ** apply env_typing_cons; sauto.
Qed.

(** Every well-typed term is strongly normalizing. *)
Lemma normalization :
  forall M T,
    Typing nil M T ->
    SN M.
Proof.
 intros M T tp.
 assert (Reducible M T).
  replace M with (subst_env 0 nil M)
   by (eapply subst_env_closed_noop; eauto).
  eapply reducibility; eauto; solve [firstorder].
 (* With reducibility comes strong normalization. *)
 solve [eauto with SN].
Qed.

(** Prints out "Closed under the global context" if we have no
remaining assumptions. *)
Print Assumptions normalization.
