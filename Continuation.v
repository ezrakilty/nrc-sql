Add LoadPath "Listkit" as Listkit.

Require Import Coq.Sets.Image.

Require Import Norm.
Require Import Rewrites.
Require Import Term.
Require Import Omega.
Require Import Shift.

Inductive Continuation :=
  Empty : Continuation
| Iterate : Term -> Continuation -> Continuation.

Fixpoint Ksize K :=
  match K with
      Empty => 0
    | Iterate _ K' => S (Ksize K')
  end.

Fixpoint plug (K : Continuation) (M : Term) : Term :=
  match K with
      Empty => M
    | Iterate N K' => plug K' (TmBind M N)
  end.

Definition SNK (K : Continuation) :=
  forall M,
    SN M ->
    SN (plug K (TmSingle M)).

Definition ReducibleK (Reducible:Term->Ty -> Type) (K : Continuation) (T : Ty) :=
    forall M,
      Reducible M T ->
      SN (plug K (TmSingle M)).

Lemma Rw_under_K:
  forall K M N,
    (M ~> N) -> (plug K M ~> plug K N).
Proof.
 induction K; simpl; intros; auto.
Qed.

Hint Resolve Rw_under_K.

Lemma plug_SN_rw:
  forall K M M',
    (M ~> M') -> SN (plug K M) -> SN (plug K M').
Proof.
 intros.
 inversion H0.
 apply H1.
 auto.
Qed.

Definition HoleType K T :=
  forall M env, Typing env M T -> {S : Ty & Typing nil (plug K M) S}.

Definition Krw K K' := (forall M, plug K M ~> plug K' M).

(** Reflexive, transitive closure of Krw *)
Inductive Krw_rt : Continuation -> Continuation -> Type :=
| Krw_rt_refl : forall m n, m = n -> Krw_rt m n
| Krw_rt_step : forall m n, Krw m n -> Krw_rt m n
| Krw_rt_trans : forall l m n, Krw_rt l m -> Krw_rt m n
                -> Krw_rt l n.

Hint Constructors Krw_rt.

Lemma iterate_reduce K K' : Krw K K' -> forall F, Krw (Iterate F K) (Iterate F K').
Proof.
 unfold Krw.
 intros.
 simpl.
 apply H.
Qed.

Lemma rw_in_K_body:
  forall K M M',
   (M ~> M') -> (Krw (Iterate M K) (Iterate M' K)).
Proof.
 intros.
 unfold Krw.
 intros.
 simpl.
 apply Rw_under_K.
 eauto.
Qed.

Hint Resolve iterate_reduce rw_in_K_body.

Lemma plug_SN_rw_rt:
  forall (K : Continuation) (M M' : Term),
  (M ~>> M') -> SN (plug K M) -> SN (plug K M').
Proof.
 intros.
 induction H; subst; eauto using plug_SN_rw.
Qed.

Inductive Ktyping : Continuation -> Ty -> Type :=
  Ktype : forall K T env S M, Typing env M T -> Typing nil (plug K M) S -> Ktyping K T.

Lemma SN_push_under_k:
  forall K M,
    SN (plug K M) ->
    SN M.
Proof.
 induction K.
  simpl.
  auto.
 intros.
 simpl in H.
 pose (s := IHK (TmBind M t) H).
 eapply SN_embedding with (f := fun x => TmBind x t) (Q := TmBind M t); sauto.
Qed.

Hint Constructors Neutral.

Fixpoint appendK K1 K2 :=
  match K1 with
    | Empty => K2
    | Iterate N K1' => Iterate N (appendK K1' K2)
  end.

Lemma Ksize_appendK:
  forall K1 K2,
    Ksize (appendK K1 K2) = Ksize K1 + Ksize K2.
Proof.
  induction K1; simpl; intros.
  - auto.
  - rewrite IHK1.
    auto.
Qed.

(* K o (x)N o (y)N0 @ M =
   K @ for x (for y M N0) N ~>
   K @ for y M (for x N0 N) =
   K o (y)(for x N0 N) @ M
 *)
Lemma assoc_in_K:
  forall N0 N K,
  Krw (Iterate N0 (Iterate N K)) (Iterate (TmBind N0 (shift 1 1 N)) K).
Proof.
 unfold Krw.
 simpl.
 intros.
 auto.
Qed.

Definition NotBind M := forall a b, M <> TmBind a b.

Lemma NotBind_TmBind L M : NotBind (TmBind L M) -> False.
Proof.
  unfold NotBind.
  unfold not.
  intro H.
  eapply H.
  eauto.
Qed.

Lemma three_ways_to_reduce_at_interface:
  forall K M Z,
    (plug K M ~> Z) ->
    {M' : Term         &              Z = plug K M' & M ~> M'} +
    {K' : Continuation &              Z = plug K' M & Krw K K'} +
    (notT (Neutral M) *
     { K' : Continuation & { M' : Term & Z = plug K' M' &
                                { t : Term & K = Iterate t K' & NotBind M } } }) +

    { K' : Continuation & Z = plug K' TmNull &
           { K'' : Continuation & K = appendK K'' (Iterate TmNull K') } } +

    { L : Term & { L' : Term & M = TmBind L L' &
        { K' : Continuation & {N : Term & K = Iterate N K' &
               Z = plug K' (TmBind L (TmBind L' (shift 1 1 N))) } } } }.
Proof.
  induction K; simpl; intros.
  - left; left; left.
    eauto.
  - clone H.
    rename H0 into H_rw.
    apply IHK in H; clear IHK.
    destruct H as [[[[[M' H0 H1] | [K' H0 H1]] | [H' [K' [M' H0 H1]]]] | [K' Zeq [K'' Keq]]] | [L [L' H0 [K' [N H1 H2]]]]].
    * inversion H1.
      { subst. left; left; right. split. introversion.
        exists K, TmNull; auto. exists t; easy. }
      { subst. left; right. exists K; auto. exists Empty; auto. }
      { subst. left; left; right. split; [introversion | ].
        exists K, (t */ x); auto. exists t; easy. }
      { subst. left; left; right. split; [introversion | ].
        exists K, (TmUnion (TmBind xs t) (TmBind ys t)); auto. exists t; easy. }
      { subst. left; left; left. eauto. }
      { subst. right. eauto. }
      { subst. left; left; left; right. exists (Iterate n' K); auto. }
    * left; left; left; right.
      exists (Iterate t K'); auto.
    * destruct H1 as [u H1 H2].
      exfalso. unfold NotBind, not in H2. eauto using H2.
    * subst.
      left; right.
      exists K'; auto.
      exists (Iterate t K''); simpl; auto.
    * left; left; left; right.
      inversion H0.
      subst.
      exists (Iterate (TmBind L' (shift 1 1 N)) K').
      simpl.
      auto.
      apply assoc_in_K.
Qed.

Lemma appendK_assoc :
  forall K0 K1 K2,
    appendK (appendK K0 K1) K2 = appendK K0 (appendK K1 K2).
Proof.
  induction K0; intros; simpl.
  - auto.
  - rewrite IHK0.
    auto.
Qed.

(* XXX: I think this is another problem in the thesis: I didn't
   adequately account for a "reduction in the context" being something
   that obliterates the subject term: K@M ~> K'@[] where
   K = K' \comp (x)[] \comp K'' for some K''. *)

Lemma Neutral_Lists:
  forall K M,
    Neutral M ->
    forall Z, (plug K M ~> Z) ->
    {M' : Term         & Z = plug K M' & M ~> M'} +
    {K' : Continuation & Z = plug K' M & Krw K K'} +
    {K' : Continuation & Z = plug K' TmNull & {K'' & K = appendK K'' K'}}.
Proof.
 intros.
 clone H0.
 rename H1 into H00.
 apply three_ways_to_reduce_at_interface in H0.
 destruct H0 as [[[[[M' H0 H1] | [K' H0 H1]] | [H' [K' [L H0 H1]]]] | [K' Zeq [K'' Keq]]] | ?].
 * left; left; eauto.
 * left; right.
   exists K'; auto.
 * destruct H1.
   inversion e.
   subst.
   contradiction.
 * right.
   exists K'.
   { auto. }
   exists (appendK K'' (Iterate TmNull Empty)).
   rewrite appendK_assoc.
   simpl.
   auto.
 * left; right.
   destruct s as [L [L' H_ [K' [N H0 H1]]]].
   subst M.
   inversion H.
Qed.

Lemma reverse_plug_defn :
  forall K L M, plug K (TmBind L M) = plug (Iterate M K) L.
Proof.
  auto.
Qed.

Lemma K_TmNull_rw:
  forall K Z,
    (plug K TmNull ~> Z) ->
    {K' : Continuation & Z = plug K' TmNull &
          { K'' : Continuation & Ksize K'' > 0 & K = appendK K'' K' } } +
    {K' : Continuation & Krw K K' & Z = plug K' TmNull}.
Proof.
 destruct K; simpl; intros Z H.
 * inversion H.
 * clone H.
   rename H0 into H_rw.
   apply three_ways_to_reduce_at_interface in H.
   destruct H as [[[[[M' Ha Hb] | [K' Ha Hb]] |  [H' [K' [M' H0 [N H1 H2]]]]] | ?] | ?].
   - inversion Hb; subst.
     ** left.
        exists K; auto.
        exists (Iterate t Empty); auto.
     ** left. exists K; auto.
        exists (Iterate TmNull Empty); auto.
     ** solve [inversion H2].
     ** right.
        exists (Iterate n' K); auto.
   - right.
     subst.
     exists (Iterate t K').
     eauto.
     auto.
   - refute.
     intuition.
     eapply H2; auto.
   - destruct s as [K' Zeq [K'' Keq]]; subst.
     left.
     exists K'; auto.
     exists (Iterate t (appendK K'' (Iterate TmNull Empty))); simpl; auto.
     { omega. }
     rewrite appendK_assoc.
     simpl.
     auto.
   - destruct s as [L [L' H0 [K' [N H1 H2]]]].
     inversion H0.
     subst.
     rewrite reverse_plug_defn.
     right.
     eauto using assoc_in_K.
Qed.

Lemma Ksize_induction P :
  (forall K, Ksize K = 0 -> P K) ->
  (forall n K', (forall K, Ksize K = n -> P K) ->
                (Ksize K' = S n) ->
                (P K')) ->
  forall K,
    P K.
Proof.
 intros H0 H_ind.
 intros K.
 pose (n := Ksize K).
 assert (n = Ksize K) by auto.
 clearbody n.
 revert n K H.
 induction n.
  auto.
 intros K H.
 destruct K.
  simpl in H; auto.
 apply H_ind with (n:=n); sauto.
Qed.

Lemma Ksize_induction_strong P :
  (forall K, (forall K', Ksize K' <  Ksize K -> P K') -> P K) ->
   forall K, P K.
Proof.
 intros X.
 cut (forall n, (forall K', Ksize K' <= n -> P K')).
 eauto.
 induction n.
 - intros.
   destruct K'; auto.
   apply X.
   simpl.
   intros.
   let T := type of H in absurd T.
   omega.
   auto.
   simpl in H; exfalso ; omega.
 - intros.
   apply X.
   intros.
   destruct (le_gt_dec (Ksize K'0) n).
   * apply IHn; auto.
   * apply X.
     intros.
     assert (Ksize K'0 = S n) by omega.
     assert (Ksize K'1 <= n) by omega.
     apply IHn.
     auto.
(* Seems like the above is dodgy; proving it twice? *)
Qed.

Fixpoint deepest_K M :=
match M with
| TmBind M' N' =>
  let (K, body) := deepest_K M' in
  (appendK K (Iterate N' Empty), body)
| _ => (Empty, M)
end.

(* Fixpoint drop_outermost K := *)
(* match K with *)
(* | Iterate t Empty => (t, Empty) *)
(* | Iterate t K' => let (f, K'') := drop_outermost K' in *)
(*                   (f, Iterate t K'') *)
(* | Empty => (TmNull, Empty) *)
(* end. *)

Lemma plug_appendK_weird:
  forall K M M',
    plug (appendK K (Iterate M Empty)) M' = TmBind (plug K M') M.
Proof.
 induction K; simpl; auto.
Qed.

Lemma deepest_K_spec:
  forall M K' M',
    deepest_K M = (K', M') ->
    plug K' M' = M.
Proof.
 induction M; simpl; intros; inversion H; auto.
 pose (X := deepest_K M1).
 assert (X = deepest_K M1) by auto.
 destruct X.
 rewrite <- H0 in H.
 inversion H.
 subst.
 pose (IHM1 c M').
 rewrite <- e; auto.
 apply plug_appendK_weird.
Qed.

Lemma appendK_Empty:
  forall K, appendK K Empty = K.
Proof.
 induction K; simpl; auto.
 rewrite IHK.
 auto.
Qed.

Lemma deepest_K_plug:
  forall K,
     forall M K' M',
       deepest_K M = (K', M') ->
       deepest_K (plug K M) = (appendK K' K, M').
Proof.
 induction K.
 - simpl.
   intros.
   rewrite appendK_Empty.
   auto.
 - simpl.
   intros.
   rewrite IHK with (K':=appendK K' (Iterate t Empty))(M':=M').
   * rewrite appendK_assoc.
     simpl.
     auto.
   * simpl.
     rewrite H.
     auto.
Qed.

Lemma deepest_K_TmTable :
  forall K t, deepest_K (plug K (TmTable t)) = (K, TmTable t).
Proof.
  intros.
  replace K with (appendK Empty K) at 2.
  apply deepest_K_plug.
  trivial.
  auto.
Qed.

Lemma deepest_K_TmNull K :
  deepest_K (plug K TmNull) = (K, TmNull).
Proof.
 pose (X := deepest_K TmNull).
 assert (X = deepest_K TmNull) by auto.
 simpl in H.
 erewrite deepest_K_plug; eauto.
 simpl.
 auto.
Qed.

Lemma unique_plug_null:
  forall K K',
    (plug K TmNull = plug K' TmNull) -> K = K'.
Proof.
 intros.
 assert (deepest_K (plug K TmNull) = (K, TmNull)).
  apply deepest_K_TmNull.
 assert (deepest_K (plug K' TmNull) = (K', TmNull)).
  apply deepest_K_TmNull.
 congruence.
Qed.

Hint Resolve unique_plug_null.

Lemma Rw_conserves_Ksize:
  forall K K',
    (plug K TmNull ~> plug K' TmNull) -> Ksize K >= Ksize K'.
Proof.
 induction K.
 - simpl.
   intros.
   inversion H.
 - simpl.
   intros.
   let T := type of H in assert (H' : T) by auto.
   apply three_ways_to_reduce_at_interface in H.
   destruct H as [[[[[M' Ha Hb] | [K0 Ha Hb]] | [Hn [K0 [M' H0 [N H1 H2]]]]] | ?] | ?].
   * inversion Hb; subst.
     -- assert (K' = K).
        { apply unique_plug_null; auto. }
        subst.
        omega.
     -- assert (K = K').
        apply unique_plug_null; auto.
        rewrite H.
        omega.
     -- inversion H2.
     -- assert (K' = Iterate n' K).
        { apply unique_plug_null.
          simpl in *; sauto. }
        subst.
        simpl.
        omega.

   * assert (K' = Iterate t K0).
     { apply unique_plug_null.
       simpl in *; sauto. }
     subst.
     replace (plug K (TmBind TmNull t)) with (plug (Iterate t K) TmNull) in H' by auto.
     simpl.
     assert (plug K TmNull ~> plug K0 TmNull) by auto.
     apply IHK in H.
     omega.

   * refute.
     apply (H2 TmNull t); auto.

   * destruct s as [K0 H [K'' Keq]].
     subst.
     assert (K' = K0) by (apply unique_plug_null; auto).
     rewrite H0.
     rewrite Ksize_appendK.
     simpl.
     omega.
   * destruct s as [L [L' H0 [K0 [N H1 H2]]]].
     subst.
     simpl.
     inversion H0.
     subst.
     assert (K' = Iterate (TmBind L' (shift 1 1 N)) K0).
     { apply unique_plug_null.
       simpl in *; sauto. }
     subst.
     simpl.
     omega.
Qed.

Lemma Krw_rt_conserves_Ksize:
  forall K K',
    Krw_rt K K' -> Ksize K >= Ksize K'.
Proof.
 intros.
 induction H.
   subst; sauto.
  specialize (k TmNull).
  apply Rw_conserves_Ksize; sauto.
 omega.
Qed.

Lemma rw_rt_preserves_plug_TmNull:
  forall (x : Continuation) (M N : Term),
    (M ~>> N) -> {x : Continuation& M = plug x TmNull} -> {y : Continuation & N = plug y TmNull}.
Proof.
 intros x M N H H0.
 induction H.
 - subst.
   eauto.
 - destruct H0.
   subst.
   apply K_TmNull_rw in r as [[K neq [K'' H0 H1]] | [K H0 H1]].
   exists K; auto.
   exists K; auto.
 - firstorder.
Qed.

Inductive prefix : Continuation -> Continuation -> Set :=
  prefix_refl : forall K, prefix K K
| prefix_frame :forall K K' N, prefix K' K -> prefix K' (Iterate N K).

Hint Constructors prefix.

Lemma prefix_breakdown :
  forall K' K,
    prefix K' K -> {K0 & K = appendK K0 K'}.
Proof.
  induction K; intros.
  - inversion H; subst.
    exists Empty; auto.
  - inversion H; subst.
    * exists Empty; auto.
    * apply IHK in H2.
      destruct H2.
      subst.
      exists (Iterate t x).
      auto.
Qed.

Lemma reexamine:
  forall K' K,
    prefix K' K
    -> forall M, {M' : Term & plug K' M' = plug K M}.
Proof.
 induction K; simpl; intros.
  inversion H.
  subst.
  simpl.
  exists M; sauto.

 inversion H.
  subst.
  exists M.

   auto.

 subst.
 pose (IHK H2 (TmBind M t)).
 destruct s.
 eauto.
Qed.

Inductive relK : Continuation -> Continuation -> Set :=
  rw : forall K K', Krw K K' -> relK K K'
| strip : forall K K' t, K = Iterate t K' -> relK K K'.

Inductive relK_rt  : Continuation -> Continuation -> Set :=
  refl : forall K, relK_rt K K
| step : forall K K', relK K K' -> relK_rt K K'
| trans : forall K K' K'', relK_rt K K' -> relK_rt K' K'' -> relK_rt K K''.

Hint Constructors relK relK_rt.

Lemma magic:
forall K K',
  relK_rt K K'
  -> forall M,
       SN (plug K M)
  -> {M' : Term & SN (plug K' M')}.
Proof.
 intros K K' rel.
 induction rel; intros M sn.
   seauto.
  destruct r.
   pose (k M).
   exists M.
   inversion sn.
   seauto.
  lapply (reexamine K' (Iterate t K')).
   intros H.
   subst.
   specialize (H M).
   destruct H.
   exists x.
   simpl in *.
   rewrite e.
   sauto.
  apply prefix_frame.
  apply prefix_refl.
 pose (s := IHrel1 M sn).
 destruct s.
 pose (IHrel2 x s).
 sauto.
Qed.

Lemma relK_rt_appendK:
  forall K K',
    relK_rt (appendK K K') K'.
Proof.
  induction K; simpl; intros.
  auto.
  eapply trans.
  apply step.
  apply strip with t.
  eauto.
  auto.
Qed.

Lemma K_TmNull_relK:
  forall K K',
    (plug K TmNull ~> plug K' TmNull)
    -> relK_rt K K'.
Proof.
 intros.
 apply K_TmNull_rw in H as [[K_shorter eq [K'' H1a H1b]] | [K'' H1a H1b]].
 - subst.
   apply unique_plug_null in eq.
   subst.
   apply relK_rt_appendK.
 - apply unique_plug_null in H1b.
   subst.
   auto.
Qed.

Definition is_K_null M := {K : Continuation & M = plug K TmNull}.

Definition gimme_K M (p : is_K_null M) := projT1 p.

Lemma K_TmNull_rw_abstract
     : forall (K : Continuation) (Z : Term),
       (plug K TmNull ~> Z) ->
       {K' : Continuation & Z = plug K' TmNull & Ksize K' <= Ksize K}.
Proof.
 intros.
 apply K_TmNull_rw in H.
 firstorder; subst.
 - eexists.
   eauto.
   rewrite Ksize_appendK.
   omega.
 - eexists; [eauto|].
   apply Krw_rt_conserves_Ksize.
   eauto.
Qed.

(* Lemma K_TmNull_rw_abstract *)
(*      : forall (K : Continuation) (Z : Term), *)
(*        (plug K TmNull ~> Z) -> *)
(*        {K' : Continuation & Z = plug K' TmNull}. *)
(* Proof. *)
(*  intros. *)
(*  apply K_TmNull_rw in H. *)
(*  destruct H; firstorder. *)
(* Qed. *)

Lemma K_TmNull_rw_rt:
  forall A Z,
    (A ~>> Z) ->
    is_K_null A -> is_K_null Z.
Proof.
 intros.
 induction H; unfold is_K_null; firstorder; subst.
  subst.
  eauto.
  apply K_TmNull_rw_abstract in r.
  firstorder.
Qed.

Lemma K_TmNull_relK_rt_inner:
  forall A Z
    (pA : is_K_null A) (pZ: is_K_null Z),
    (A ~>> Z) ->
    relK_rt (gimme_K A pA) (gimme_K Z pZ).
Proof.
 intros.
 induction H; destruct pA; destruct pZ; subst; simpl in *.
   apply unique_plug_null in e.
   subst.
   apply refl.
  apply K_TmNull_rw in r as [[K' H1a [K'' Ksize_K'' H1b]] | [K' H1a H1b]].
   subst.
   assert (x0 = K') by (apply unique_plug_null; auto).
   subst.
   apply relK_rt_appendK.
  assert (x0 = K') by (apply unique_plug_null; auto).
  subst.
  auto.
 assert (is_K_null (plug x TmNull)).
  unfold is_K_null.
  eauto.
 specialize (IHRewritesTo_rt1 H1).
 assert (is_K_null m).
  apply K_TmNull_rw_rt with (A := plug x TmNull); auto.
 specialize (IHRewritesTo_rt1 H2).
 replace (gimme_K (plug x TmNull) H1) with x in IHRewritesTo_rt1.
  apply trans with (gimme_K m H2); auto.
  assert (H3 : is_K_null (plug x0 TmNull)).
   unfold is_K_null.
   eauto.
  specialize (IHRewritesTo_rt2 H2 H3).
  replace (gimme_K (plug x0 TmNull) H3) with x0 in IHRewritesTo_rt2.
   exact IHRewritesTo_rt2.
  unfold gimme_K.
  unfold projT1.
  destruct H3.
  apply unique_plug_null; auto.
 unfold gimme_K.
 unfold projT1.
 destruct H1.
 apply unique_plug_null; auto.
Qed.

Lemma K_TmNull_relK_rt:
  forall K K',
    (plug K TmNull ~>> plug K' TmNull)
    -> relK_rt K K'.
Proof.
 intros.
 assert (is_K_null (plug K TmNull)).
  unfold is_K_null.
  eauto.
 assert (is_K_null (plug K' TmNull)).
  unfold is_K_null.
  eauto.
 eapply K_TmNull_relK_rt_inner in H; eauto.
 replace (gimme_K (plug K TmNull) H0) with K in H.
  replace (gimme_K (plug K' TmNull) H1) with K' in H.
   auto.
  destruct H1.
  simpl.
  auto using unique_plug_null.
 destruct H0.
 simpl.
 auto using unique_plug_null.
Qed.

Lemma Krw_rt_Rw_rt:
  forall K K' M, Krw_rt K K' -> (plug K M ~>> plug K' M).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_under_K:
  forall K M N,
    (M ~>> N) -> (plug K M ~>> plug K N).
Proof.
 intros K M N red.
 induction red.
   subst; auto.
  eauto using Rw_rt_step, Rw_under_K.
 eauto.
Qed.

(* (* TODO: Should be able to get "induction on Krw sequences" directly
      from SN . plug like this: *)
SN (plug K M) ->
(forall K0, Krw_rt K K0 -> (forall K', Krw K0 K' -> (P K' -> P K0))) ->
P K.
 *)

Lemma Rw_rt_conserves_Ksize:
  forall K K',
    (plug K TmNull ~>> plug K' TmNull) -> Ksize K >= Ksize K'.
Proof.
 intros.
 apply rw_rt_f_induction
   with (A := Continuation)
        (f := fun k => plug k TmNull)
        (x := K)
        (R := fun k k' => Ksize k >= Ksize k') in H.
 - destruct H as [x e [x0 e0 g]].
   apply unique_plug_null in e.
   apply unique_plug_null in e0.
   subst.
   auto.
 - eauto.
 - intros; omega.
 - unfold injective.
   apply unique_plug_null.
 - intros.
   eauto using rw_rt_preserves_plug_TmNull.
 - apply Rw_conserves_Ksize; auto.
 - auto.
Qed.

Lemma plug_rw_rt:
  forall K K' M M', Krw_rt K K' -> (M ~>> M') -> (plug K M ~>> plug K' M').
Proof.
 intros.
 assert (plug K M ~>> plug K' M).
 apply Krw_rt_Rw_rt; auto.
 assert (plug K' M ~>> plug K' M').
 { apply Rw_rt_under_K; auto. }
 eauto.
Qed.

Lemma plug_appendK:
  forall (K K' : Continuation) (M : Term),
  plug (appendK K K') M = plug K' (plug K M).
Proof.
  induction K; simpl; intros.
  auto.
  rewrite IHK.
  auto.
Qed.

Lemma curtailment:
  forall K' K M,
    plug (appendK K (Iterate TmNull K')) M ~> plug K' TmNull.
Proof.
  induction K; simpl; intros.
  apply Rw_under_K.
  auto.
  rewrite plug_appendK.
  simpl.
  apply Rw_under_K.
  auto.
Qed.

Lemma Krw_appendK:
  forall K K' K1,
    Krw K K' ->
    Krw (appendK K1 K) (appendK K1 K').
Proof.
 induction K1; simpl; auto.
Qed.

Lemma prefix_appendK:
  forall K0 K K',
    prefix K0 K' ->
    prefix K0 (appendK K K').
Proof.
 induction K; simpl; auto.
Qed.
