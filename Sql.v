Load "eztactics.v".

Add LoadPath "Listkit" as Listkit.

Require Import Term.

(* To do: Need a "table" form. *)
Require Import Bool.

Definition is_basic_type T := T = TyBase.

Inductive is_row_type : Ty -> Type :=
| row_type_wit : forall s t, is_basic_type s -> is_basic_type t -> is_row_type (TyPair s t).

Inductive is_relation_type : Ty -> Type :=
| relation_type_wit : forall t, is_row_type t -> is_relation_type (TyList t).

Fixpoint is_basic_form B :=
  match B with
  | TmIf B1 B2 B3 => is_basic_form B1 && is_basic_form B2 && is_basic_form B3
  | TmProj b (TmVar x) => true
  | TmConst => true
  | _ => false
  end.

Fixpoint is_row_form R :=
  match R with
  | TmPair b1 b2 => is_basic_form b1 && is_basic_form b2
  | TmVar x => true
  | _ => false
  end.

Fixpoint is_filtered_relation Z :=
  match Z with
  | TmIf b Z TmNull => is_basic_form b && is_filtered_relation Z
  | TmSingle R => is_row_form R
  | TmTable t => true
  | _ => false
  end.

Fixpoint is_joined_relation F :=
  match F with
  | TmBind (TmTable t) F => is_joined_relation F
  | _ => is_filtered_relation F
  end.

Fixpoint is_in_sql_like_sublang M :=
  match M with
  | TmUnion M1 M2 => is_in_sql_like_sublang M1 && is_in_sql_like_sublang M2
  | TmNull => true
  | _ => is_joined_relation M
  end.

Require Import Rewrites.

Definition Rewrites M := {N:Term & (M ~> N) }.

Hint Unfold Rewrites.

Definition Normal M := notT (Rewrites M).

Hint Transparent Rewrites Normal.

Lemma Normal_sub_TmPair_1 : forall M N,
    Normal (TmPair M N) -> Normal M.
Proof.
Admitted.

Lemma Normal_sub_TmPair_2 : forall M N,
    Normal (TmPair M N) -> Normal N.
Proof.
Admitted.

Lemma Normal_sub_TmUnion_1 : forall M N,
    Normal (TmUnion M N) -> Normal M.
Proof.
Admitted.

Lemma Normal_sub_TmUnion_2 : forall M N,
    Normal (TmUnion M N) -> Normal N.
Proof.
Admitted.

Lemma Normal_sub_TmBind_1 : forall M N,
    Normal (TmBind M N) -> Normal M.
Proof.
Admitted.

Lemma Normal_sub_TmBind_2 : forall M N,
    Normal (TmBind M N) -> Normal N.
Proof.
Admitted.

Lemma Normal_sub_TmProj : forall b M,
    Normal (TmProj b M) -> Normal M.
Proof.
Admitted.

Lemma Normal_sub_TmSingle : forall M,
    Normal (TmSingle M) -> Normal M.
Proof.
Admitted.

Lemma Normal_sub_TmApp_1 : forall L M,
    Normal (TmApp L M) -> Normal L.
Proof.
Admitted.

Lemma Normal_sub_TmApp_2 : forall L M,
    Normal (TmApp L M) -> Normal M.
Proof.
Admitted.

Hint Resolve Normal_sub_TmPair_1 Normal_sub_TmPair_2 Normal_sub_TmUnion_1 Normal_sub_TmUnion_2
     Normal_sub_TmBind_1 Normal_sub_TmBind_2
     Normal_sub_TmProj Normal_sub_TmSingle
     Normal_sub_TmApp_1 Normal_sub_TmApp_2.

Hint Extern 1 (Normal ?M) =>
match goal with
| H : Normal (TmPair ?N M) |- _ => eapply Normal_sub_TmPair_2; eauto
| H : Normal (TmPair M ?N) |- _ => eapply Normal_sub_TmPair_1; eauto

| H : Normal (TmUnion M ?N) |- _ => eapply Normal_sub_TmUnion_1; eauto
| H : Normal (TmUnion ?N M) |- _ => eapply Normal_sub_TmUnion_2; eauto

| H : Normal (TmBind M ?N) |- _ => eapply Normal_sub_TmBind_1; eauto
| H : Normal (TmBind ?N M) |- _ => eapply Normal_sub_TmBind_2; eauto

| H : Normal (TmProj ?b M) |- _ => eapply Normal_sub_TmProj; eauto
| H : Normal (TmSingle M) |- _ => eapply Normal_sub_TmSingle; eauto

| H : Normal (TmApp M ?N) |- _ => eapply Normal_sub_TmApp_1; eauto
| H : Normal (TmApp ?N M) |- _ => eapply Normal_sub_TmApp_2; eauto
end.

Axiom var_not_closed: forall x T, notT(Typing nil (TmVar x) T).

Ltac bogus_normal H :=
  exfalso; apply H; eauto.

(* Note: Missing in the thesis: The inductive premise that M's typing
   env defines only variables of basic, row or relation type. *)

Require Import Lists.List.

Lemma row_type_in_row_env:
  forall T env x,
  (forall s : Ty, In s env -> is_row_type s) ->
    value T = nth_error env x ->
    is_row_type T.
Proof.
  intros.
  apply H.
  eauto using nth_error_In.
Qed.

Definition is_row_type_env env :=
  forall T n,
  value T = nth_error env n -> is_row_type T.

Lemma row_env_Normal_forms:
  forall M T env,
    Normal M ->
    is_row_type_env env ->
    Typing env M T ->
    (match T return Type with
     | TyBase => {b : bool & {x : nat & M = TmProj b (TmVar x)}} + (M = TmConst)
     | TyPair _ _ =>
       {x : nat & M = TmVar x} + {m : Term & {n : Term & M = TmPair m n}}
     | TyArr _ _ => {N : Term & M = TmAbs N}
     | TyList _ =>
       {T : Ty & {N : Term & M = TmBind (TmTable T) N}} +
       {M1 & {M2 & M = TmUnion M1 M2}} +
       {N & M = TmSingle N} +
       {T : Ty & M = TmTable T} +
       (M = TmNull)
    end).
Proof.
  induction M; intros T env Normal_M env_typs H; inversion H; subst;
    (try (solve [split; intros S0 T0 H0; discriminate])).

  - auto.
  - assert (is_row_type T) by (eauto using row_type_in_row_env).
    destruct T;
      try (inversion H0).
    left; eauto.

  - right; eauto.

  - assert (Normal M) by auto.
    specialize (IHM (TyPair T t) env H0 env_typs H3).
    simpl in IHM.
    destruct IHM as [[x Heq] | [m [n Heq]]].
    * destruct T; intuition; try discriminate.

      -- subst.
         left; eexists.
         eauto.

         (* Hmm, three repeated cases follow... *)
      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair (TyPair T1 T2) t)) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H6.

      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair (TyArr T1 T2) t)) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H6.

      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair (TyList T) t)) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H6.

    * subst.
      unfold Normal in H.
      lapply Normal_M; try easy.
      unfold Rewrites.
      eauto.

  - (* The TmProj true case; exactly parallel to the above. Must automate or something...*)
    assert (Normal M) by auto.
    specialize (IHM (TyPair s T) env H0 env_typs H3).
    simpl in IHM.
    destruct IHM as [[x Heq] | [m [n Heq]]].
    * destruct T; intuition; try discriminate.

      -- subst.
         left; eexists.
         eauto.

      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair s (TyPair T1 T2))) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H7.

      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair s (TyArr T1 T2))) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H7.

      -- exfalso.
         subst M.
         inversion H3; subst.
         assert (is_row_type (TyPair s (TyList T))) by (eauto using row_type_in_row_env).
         inversion H1.
         inversion H7.

    * subst.
      unfold Normal in H.
      lapply Normal_M; try easy.
      unfold Rewrites.
      eauto.

  - eauto.

  - exfalso.
    assert (H0 : Normal M1) by auto.
    specialize (IHM1 (TyArr a T) env H0 env_typs H2).
    simpl in IHM1.
    destruct IHM1 as [N Neq].
    subst M1.
    unfold Normal in Normal_M.
    unfold Rewrites in Normal_M.
    apply Normal_M.
    eauto.
    Unshelve.
    exact 0.

  - auto.
  - eauto.
  - eauto 7.
  - assert (H0 : Normal M1) by auto.
    specialize (IHM1 (TyList s) env H0 env_typs H2).
    simpl in IHM1.
    destruct IHM1 as [[[[[T [N M1eq]] |
                         [M11 [M12 M1eq]]] |
                        [N M1eq]] |
                       [T M1eq]] |
                      ?];
      try (solve [subst; bogus_normal Normal_M]).
    subst.
    eauto 7.
  - eauto.
Unshelve.
exact 0.
Qed.

Inductive is_basic_formi : Term -> Type :=
| is_basic_formi_1 : forall b1 b2 b3,
    is_basic_formi b1 -> is_basic_formi b2 -> is_basic_formi b3 -> is_basic_formi (TmIf b1 b2 b3)
| is_basic_formi_2 : forall b x, is_basic_formi (TmProj b (TmVar x))
| is_basic_formi_3 : is_basic_formi TmConst
.

Inductive is_row_formi : Term -> Type :=
| is_row_formi_1 :
    forall b1 b2, is_basic_formi b1 -> is_basic_formi b2 -> is_row_formi (TmPair b1 b2)
| is_row_formi_2 : forall x, is_row_formi (TmVar x)
.

Inductive is_filtered_relationi : Term -> Type :=
| is_filtered_relationi_1 :
    forall b Z,
      is_basic_formi b -> is_filtered_relationi Z -> is_filtered_relationi (TmIf b Z TmNull)
| is_filtered_relationi_2 : forall R, is_row_formi R -> is_filtered_relationi (TmSingle R)
| is_filtered_relationi_3 : forall t, is_filtered_relationi (TmTable t)
.

Inductive is_joined_relationi : Term -> Type :=
| is_joined_relationi_1 :
    forall t F, is_joined_relationi F -> is_joined_relationi (TmBind (TmTable t) F)
| is_joined_relationi_2 : forall F, is_filtered_relationi F -> is_joined_relationi F
.

Inductive is_in_sql_like_sublangi : Term -> Type :=
| is_in_sql_like_sublangi_1 :
    forall M1 M2,
      is_in_sql_like_sublangi M1 -> is_in_sql_like_sublangi M2 ->
      is_in_sql_like_sublangi (TmUnion M1 M2)
| is_in_sql_like_sublangi_2 :
    is_in_sql_like_sublangi TmNull
| is_in_sql_like_sublangi_3 : forall M, is_joined_relationi M -> is_in_sql_like_sublangi M
.

Hint Constructors is_in_sql_like_sublangi is_joined_relationi is_filtered_relationi is_row_formi is_basic_formi.

Lemma SQL_Normal_forms:
  forall M T env,
    Normal M ->
    is_row_type_env env ->
    Typing env M T ->
    (is_basic_type T -> is_basic_formi M) *
    (is_row_type T -> is_row_formi M) *
    (is_relation_type T -> is_in_sql_like_sublangi M).
Proof.
  induction M; intros T env Normal_M env_typs H;
    pose (X:=row_env_Normal_forms _ T env Normal_M env_typs H);
    inversion H; subst T.

  - repeat split; intro Z; inversion Z; eauto.

  - apply env_typs in H1.
    repeat split; intro Z.
    * destruct ty; inversion H1; inversion Z.
    * auto.
    * destruct ty; inversion H1; inversion Z.

  - repeat split; intro Z; inversion Z; eauto.

    assert (is_basic_formi M1).
    { assert (Normal_M1:Normal M1) by auto.
      apply (IHM1 _ _ Normal_M1 env_typs H2); auto. }
    assert (is_basic_formi M2).
    { assert (Normal_M2:Normal M2) by auto.
      apply (IHM2 _ _ Normal_M2 env_typs H4); auto. }
    auto.

  - repeat split; intro Z; inversion Z; subst.
    destruct X as [s | s].
    destruct s as [b [x eq]].
    inversion eq.
    auto.

    inversion s.

    destruct X as [s | s].
    destruct s as [x eq].
    inversion eq.
    destruct s as [m [n eq]].
    inversion eq.
    destruct X as [[[[X | X] | X] | X] | X].
    destruct X as [T [N eq]].
    discriminate.
    destruct X as [M1 [M2 eq]].
    discriminate.
    destruct X as [N eq].
    discriminate.
    destruct X as [T eq].
    discriminate.
    discriminate.

  - admit (* Other proj case *).

  - repeat split; intro Z; inversion Z; eauto.

  - subst.
    assert (Normal M1) by auto.
    pose (Y := row_env_Normal_forms M1 _ env H0 env_typs H2).
    simpl in Y.
    destruct Y as [N eq].
    subst.
    bogus_normal Normal_M.

  - repeat split; intro Z; inversion Z; eauto.

  - repeat split; intro Z; inversion Z; eauto.

    subst.
    assert (Normal M) by auto.
    specialize (IHM _ _ H0 env_typs H1); destruct IHM as [[? ?] ?].
    auto.

  - repeat split; intro Z; inversion Z; eauto.
    assert (Normal M1) by auto.
    assert (Normal M2) by auto.
    specialize (IHM1 _ _ H6 env_typs H2); destruct IHM1 as [[? ?] ?].
    specialize (IHM2 _ _ H7 env_typs H4); destruct IHM2 as [[? ?] ?].
    apply is_in_sql_like_sublangi_1; auto.

  - repeat split; intro Z; inversion Z; eauto.
    assert (Normal M1) by auto.
    assert (Normal M2) by auto.
    assert (H8 : {t& M1 = TmTable t}).
    pose (Y := row_env_Normal_forms M1 _ env H6 env_typs H2).
    simpl in Y.
    destruct Y as [[[[Y | Y] | Y] | Y] | Y].
    destruct Y as [T [N eq]]; subst.
    bogus_normal Normal_M.
    destruct Y as [M11 [M12 eq]]; subst.
    bogus_normal Normal_M.
    destruct Y as [N eq]; subst.
    bogus_normal Normal_M.
    destruct Y as [T eq]; subst.
    eauto.
    subst.
    bogus_normal Normal_M.
    destruct H8 as [T eq]; subst.
    apply is_in_sql_like_sublangi_3.
    apply is_joined_relationi_1.
    assert (is_row_type s).
    admit (* Need to limit the type of each TmTable somehow! *).
    assert (H8 : is_row_type_env (s :: env)).
    { intros.
      unfold is_row_type_env.
      intros.
      destruct n.
      simpl in H1.
      inversion H1.
      auto.
      assert (value T0 = nth_error env n).
      auto.
      apply env_typs in H3.
      auto. }
    specialize (IHM2 (TyList t) (s :: env) H7 H8 H4).
    destruct IHM2 as [[IHM2 IHM2'] IHM2''].
    lapply IHM2''.
    intros.
    destruct M2; inversion H1; auto.
    bogus_normal Normal_M.
    admit (* Missing a rewrite rule for TmBind (TmTable x) TmNull *).
    bogus_normal Normal_M.
    admit (* Missing a rewrite rule for TmBind (TmTable x) (TmUnion x y) *).
    auto.
  - repeat split.
    intro H0; inversion H0.
    intro H0; inversion H0.
    intro H0.
    auto.
Unshelve. (* ?? *)
exact 0.
exact 0.
Admitted.

Lemma SQL_Normal_form:
  forall M T,
    Normal M ->
    Typing nil M T ->
    is_relation_type T -> is_in_sql_like_sublangi M.
Proof.
  intros.
  lapply (SQL_Normal_forms M T nil H).
  intros H2.
  specialize (H2 H0).
  apply H2; auto.
  unfold is_row_type_env.
  intros.
  rewrite NthError.nth_error_nil in H2.
  easy.
Qed.
