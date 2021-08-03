(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Require Import Arith.
Require Import List.

Add LoadPath "Listkit" as Listkit.

Require Import Listkit.NthError.

Require Import Lia.
Require Import Shift.
Require Import Subst.
Require Import Term.

(** Let's make [N */ L] a notation for the result of a beta-reduction
    (including all the de Bruijn monkeying). Makes the lemmas a lot easier to read.
    Precedence is not correct. *)
Notation "N */ L" := (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)) (at level 99).

Lemma beta_reduct_typing_general_var:
  forall S env' x T M env k,
   k = length env ->
   Typing env' M S ->
   Typing (env ++ (S :: env')) (TmVar x) T ->
      Typing (env ++ env')
             (unshift k 1 (subst_env k (shift 0 (k + 1) M :: nil) (TmVar x)))
	     T.
Proof.
 intros S env' x.
 intros T M env k k_def M_tp N_tp; simpl; inversion N_tp; eauto.
 subst.
 assert (H: x < length (env++(S::env'))).
  eapply nth_error_to_length; eauto.
 rewrite app_length in H.
 simpl in H.
 destruct (le_gt_dec (length env) x).
  destruct (eq_nat_dec x (length env)).
   (* 'x' points to the type 'S' *)
   subst x.
   replace (length env - length env) with 0 by lia.
   simpl.
   rewrite fancy_unshift_shift; auto; [|lia].
   replace (length env+1-1) with (length env); auto; [|lia].
   replace (env++env') with (nil++env++env'); auto.
   eapply shift_preserves_typing with env'; auto.
   apply nth_error_app in H0; auto.
   replace (length env - length env) with 0 in H0 by lia.
   simpl in H0.
   inversion H0.
   auto.
  (* 'x' is in the second environment. *)
  assert (length env < x) by lia.
  assert (0 < x-length env) by lia.
  replace (nth_error (shift 0 (length env + 1) M::nil) (x-length env))
    with (error : option Term).
   simpl.
   apply TVar.
   unfold unshift_var.
   destruct (le_gt_dec (1 + length env) x); [ | lia].
   apply nth_error_app in H0; auto.
   replace (S::env') with ((S::nil)++env') in H0; auto.
   apply nth_error_app in H0; auto.
   simpl in H0.
   rewrite rewrite_nth_error_app.
    replace (x - 1 - length env) with (x - length env - 1) by lia.
    auto.
   lia.

  (* Prove that nth_error (_::nil) z = error when z > 0. *)
  symmetry; apply nth_error_overflow.
  simpl.
  lia.

 (* x is in the first environment *)
 apply TVar.
 replace (unshift_var (length env) 1 x) with x.
  rewrite nth_error_ext_length; auto.
  rewrite nth_error_ext_length in H0; auto.
 rewrite unshift_var_lo; auto.
Qed.

(** Beta reduction preserves types:
      [E      |- N{M/k} : T] when
      [E, x:S |- N : T] and
      [E      |- M : S]
*)
Lemma beta_reduct_typing_general:
  forall S env' N T M env k,
   k = length env ->
   Typing env' M S ->
   Typing (env ++ (S :: env')) N T ->
      Typing (env ++ env')
             (unshift k 1 (subst_env k (shift 0 (k + 1) M :: nil) N))
	     T.
Proof.
 induction N; intros T M env k k_def M_tp N_tp; simpl; inversion N_tp; eauto.
(* TmVar *)
 - eapply beta_reduct_typing_general_var; seauto.

(* TmAbs *)
 - apply TAbs.
   replace (s :: env ++ env') with ((s :: env) ++ env') by auto.
   rewrite shift_shift.
   replace (1 + (k + 1)) with (Datatypes.S k + 1) by auto.
   apply IHN; simpl; auto.

(* TmBind *)
 - apply TBind with s.
   apply IHN1; sauto.
   (* copy and paste of TmAbs case :-( *)
   replace (s :: env ++ env') with ((s :: env) ++ env') by auto.
   rewrite shift_shift.
   replace (1 + (k + 1)) with (Datatypes.S k + 1) by auto.
   apply IHN2; simpl; auto.
Qed.

(** Beta reduction preserves types, specialized to reduce at the head
    of the environment. *)
Lemma beta_reduct_typing:
  forall S env' N T M,
   Typing env' M S ->
   Typing (S :: env') N T ->
      Typing env' (N */ M) T.
Proof.
 intros.
 replace env' with (nil++env'); auto.
 eapply beta_reduct_typing_general; eauto.
Qed.

(** The rewrite system. The object of our study. *)
Inductive RewritesTo : Term -> Term -> Type :=
| Rw_beta : forall N M V,
    V = (N */ M) ->
    RewritesTo (TmApp (TmAbs N) M) V
| Rw_App_left : forall m1 m2 n,
    RewritesTo m1 m2 ->
    RewritesTo (TmApp m1 n) (TmApp m2 n)
| Rw_App_right : forall m n1 n2,
    RewritesTo n1 n2 ->
    RewritesTo (TmApp m n1) (TmApp m n2)
| Rw_Abs_body : forall n n',
    RewritesTo n n' ->
    RewritesTo (TmAbs n) (TmAbs n')
| Rw_Pair_left : forall m1 m2 n,
    RewritesTo m1 m2 ->
    RewritesTo (TmPair m1 n) (TmPair m2 n)
| Rw_Pair_right : forall m n1 n2,
    RewritesTo n1 n2 ->
    RewritesTo (TmPair m n1) (TmPair m n2)
| Rw_Proj : forall m1 m2 b,
    RewritesTo m1 m2 ->
    RewritesTo (TmProj b m1) (TmProj b m2)
| Rw_Proj_beta1 : forall m n,
    RewritesTo (TmProj false (TmPair m n)) m
| Rw_Proj_beta2 : forall m n,
    RewritesTo (TmProj true (TmPair m n)) n
| Rw_Union_left : forall M N M',
    RewritesTo M M' ->
    RewritesTo (TmUnion M N) (TmUnion M' N)
| Rw_Union_right : forall M N N',
    RewritesTo N N' ->
    RewritesTo (TmUnion M N) (TmUnion M N')
| Rw_Bind_null : forall n,
    RewritesTo (TmBind TmNull n) TmNull
| Rw_Bind_null_body : forall m,
    RewritesTo (TmBind m TmNull) TmNull
| Rw_Bind_beta : forall n x V,
    V = (n */ x) -> RewritesTo (TmBind (TmSingle x) n) V
| Rw_Bind_union : forall n xs ys,
    RewritesTo (TmBind (TmUnion xs ys) n) (TmUnion (TmBind xs n) (TmBind ys n))
(* TODO: The Union-Body rule does not yet work. More sophisticated Continuation representations are needed to handle it. See the git branch union-body for the first attempt. *)
(* | Rw_Bind_union_body : forall m xs ys, *)
(*     RewritesTo (TmBind m (TmUnion xs ys)) (TmUnion (TmBind m xs) (TmBind m ys)) *)
| Rw_Bind_sesubject : forall m n m',
    RewritesTo m m' -> RewritesTo (TmBind m n) (TmBind m' n)
| Rw_Bind_assoc : forall l m n,
    RewritesTo (TmBind (TmBind l m) n) (TmBind l (TmBind m (shift 1 1 n)))
| Rw_Bind_body : forall m n n',
                   RewritesTo n n' -> RewritesTo (TmBind m n) (TmBind m n')
| Rw_Single : forall m m',
                RewritesTo m m' -> RewritesTo (TmSingle m) (TmSingle m')
| Rw_If_cond: forall b1 b2 m n,
    RewritesTo b1 b2 -> RewritesTo (TmIf b1 m n) (TmIf b2 m n)
| Rw_If_left: forall b m1 m2 n,
    RewritesTo m1 m2 -> RewritesTo (TmIf b m1 n) (TmIf b m2 n)
| Rw_If_right: forall b m n1 n2,
    RewritesTo n1 n2 -> RewritesTo (TmIf b m n1) (TmIf b m n2)
| Rw_If_split: forall b m n,
    (* Not quite right; the b should be negated. And this is only at list type. *)
    RewritesTo (TmIf b m n) (TmUnion (TmIf b m TmNull) (TmIf b n TmNull))
| Rw_If_Bind: forall b m n,
    RewritesTo (TmIf b (TmBind m n) TmNull)
               (TmBind m (TmIf (shift 0 1 b) n TmNull))
.

Hint Constructors RewritesTo.

Notation "M ~> M'" := (RewritesTo M M') (at level 100).

(** Reflexive, transitive closure of RewritesTo *)
Inductive RewritesTo_rt : Term -> Term -> Type :=
| Rw_rt_refl : forall m n, m = n -> RewritesTo_rt m n
| Rw_rt_step : forall m n, RewritesTo m n -> RewritesTo_rt m n
| Rw_rt_trans : forall l m n, RewritesTo_rt l m -> RewritesTo_rt m n
                -> RewritesTo_rt l n.

Notation "M ~>> M'" := (RewritesTo_rt M M') (at level 100).

Hint Constructors RewritesTo_rt.

(** Recognizes an empty reduction sequence. *)
Fixpoint Is_empty_Rw_rt (a z : Term) (redn : a ~>> z) :=
  match redn with
    | Rw_rt_refl _ _ _ => True
    | Rw_rt_step _ _ _ => False
    | Rw_rt_trans a b z r1 r2 =>
      Is_empty_Rw_rt a b r1 /\ Is_empty_Rw_rt b z r2
  end.

(** When we know a reduction sequence "is empty," we know its start
    and end terms are equal. *)
Lemma empty_Rw_rt_elim:
  forall l m redn,
    Is_empty_Rw_rt l m redn -> l = m.
Proof.
 intros l m redn H. induction redn.
   auto.
  simpl in H.
  contradiction.
 simpl in H.
 intuition.
 congruence.
Qed.

(** A transitive reduction sequence is either empty or decomposable
    into a first step and the remainder. *)
Lemma Rw_rt_destruct:
  forall a z,
    forall redn: a ~>> z,
       (Is_empty_Rw_rt a z redn) + {x : Term & (a ~> x) & (x ~>> z)}.
(* TODO: A bit ugly! *)
Proof.
 intros.
 induction redn.
 - left.
   simpl.
   auto.
 - right.
   eauto.
 - destruct IHredn1 as [lm_empty | s];
   destruct IHredn2 as [mn_empty | s0].
   * left; simpl; auto.
   * apply empty_Rw_rt_elim in lm_empty.
     subst. right; auto.
   * apply empty_Rw_rt_elim in mn_empty.
     subst. right; auto.
   * destruct s as [x l_x x__m].
     destruct s0 as [y m_y y__n].
     right; eauto.
Qed.

(** Any reduction sequence with a last step also has a first step,
    which we can construct. *)
Lemma last_step_first_step_lemma:
  forall a y,
(*
  Would be cute with notation
  (a ~>> y ~> z) -> {x : Term & (a ~> x ~>> z)}.
*)
  (a ~>> y) -> forall z, (y ~> z) -> {x : Term & (a ~> x) & (x ~>> z)}.
Proof.
 intros a y H_a_downto_y.
 intros.
 pose (redn := Rw_rt_trans a y z H_a_downto_y (Rw_rt_step _ _ H)).
 destruct (Rw_rt_destruct a z redn).
  subst redn.
  simpl in *.
  intuition.
 auto.
Qed.

(** The rewrite relation preserves the [Typing] judgment. *)
Lemma Rw_preserves_types:
  forall M M',
    (M ~> M') ->
    forall env T,
      Typing env M T -> Typing env M' T.
Proof.
 intros M M' red.
 induction red;
    intros env T T_tp;
    inversion T_tp as
        [| | | ? ? S T' TmAbs_N_tp | | ? ? ? H | ? ? ? H | ? ? H | | | ? ? ? ? H H0 |];
    eauto.
 (* Case Beta_reduction -> *)
 - inversion TmAbs_N_tp.
   subst.
   eapply beta_reduct_typing; eauto.
 (* Case Beta reduction TPair (1) *)
 - subst.
   inversion H; sauto.
 (* Case Beta reduction TPair (2) *)
 - subst.
   inversion H; sauto.
 (* Case Beta reduction [] *)
 - inversion H.
   subst.
   eauto using beta_reduct_typing.
 (* Case TmUnion/TmBind *)
 - inversion H.
   subst.
   eauto.
 (* Case TmBind_assoc *)
 - inversion H.
   subst.
   eapply TBind; eauto.
   eapply TBind; eauto.
   replace (s :: s0 :: env) with ((s::nil) ++ (s0::nil) ++ env) by auto.
   eapply shift_preserves_typing; eauto.
Qed.

(** The reflexive-transitive rewrite relation preserves the [Typing] judgment. *)
Lemma Rw_rt_preserves_types:
  forall env M M' T,
    Typing env M T -> (M ~>> M') -> Typing env M' T.
Proof.
 intros env M M' T M_tp M_red_M'.
 induction M_red_M'; eauto using Rw_preserves_types; try congruence.
Qed.

Hint Resolve Rw_rt_preserves_types.

Require Import Listkit.All.
Require Import Listkit.AllType.
Require Import Listkit.Sets.
Require Import OutsideRange.

Lemma commute_subst_with_beta_reduct:
 (** Diagrammatically:

      (1) -----------> (2) -----------> (4)
         subst 0 {M''}      unshift 0 1
       ^                                 ^
       |                                 |
       | subst n+1 env'                  | subst n env
       |                                 |

       N ----------->  (3) ----------->  N */ M
         subst 0 {M'}      unshift 0 1

       where
           env' = map shift01 env
           M'   = shift01 M
           M''  = shift01 (subst n env M)
 *)
  forall N M n env,
    subst_env n env (N */ M) =
    (subst_env (S n) (map (shift 0 1) env) N */ subst_env n env M).
Proof.
 intros.

 (* Push subst_env inside unshift. *)
 rewrite subst_unshift (*if this used outside_range, how would it be different? *);
   [ | lia | ].
  f_equal.

  (* From here on we're just working with the left-hand square of the above diagram,

      (1) -----------> (2)
         subst 0 {M''}
       ^                ^
       |                |
       | subst n+1 env' | subst n+1 env'
       |                |

       N ------------> (3)
         subst 0 {M'}

   *)

  replace (n+1) with (S n) by lia.

  remember (shift 0 1 M) as M'.
  remember (shift 0 1 (subst_env n env M)) as M''.
  remember (map (shift 0 1) env) as env'.

  (* Push shift inside subst_env in M''. *)
  rewrite shift_subst_commute_lo in HeqM'' by lia.
  replace (n+1) with (S n) in HeqM'' by lia.

  (* We have reduced the problem to subst_factor and some obligations. *)
  rewrite <- subst_factor. (* with m:= 0, n:= S n *)
    subst; sauto.

  (* Obligations of subst_factor: *)
  (* Obl 1: All freevars of every term in [map (shift 0 1) env] are not in
     the env_domain of _::nil, i.e. the interval [0,1). *)
   unfold in_env_domain.
   simpl.
   subst env'.
   apply all_map_image.
   intros X.
   pose (shift_freevars_range X 0).
   eapply all_cut; [|apply a].
   firstorder lia.

  (* Obl 2: Substitutions do not overlap:
       (0, [_]) does not overlap (S n, _). *)
  simpl.
  solve [lia].

 (* Obligations of subst_unshift: *)
 (* Obl 1: That fvs of N{[shift 0 1 M]/0} are all outside [0,1). *)
    (* TODO some redundancy with the above obl 1 *)
 pose (fvs_M := freevars (shift 0 1 M)).
 pose (fvs_N := freevars N).
 remember (freevars (subst_env 0 (shift 0 1 M :: nil) N)) as fvs.
 (* Assert: fvs ⊆ (fvs_N ∖ {0}) ∪ fvs_M *)
 assert (H : incl_sets _
                 fvs
                 (set_union eq_nat_dec
                   fvs_M
                   (set_filter _
                        (fun x => outside_range 0 (1+0) x) fvs_N))).
  subst fvs fvs_M fvs_N.
  replace (freevars (shift 0 1 M))
     with (set_unions _ eq_nat_dec (map freevars (shift 0 1 M :: nil)))
       by auto.
  apply subst_Freevars; sauto.

 (* Now we have H : fvs ⊆ (fvs_N ∖ {0}) ∪ fvs_M *)
 (* TODO: From here out, basically just set math, plus shift_freevars_range *)
 eapply all_Type_incl.
  apply H.
 apply all_Type_union_fwd.
 split.
  subst fvs_M.
  pose (shift_freevars_range M 0). (* only need another step because all /= all_Type. *)
  firstorder lia.
 apply all_Type_filter.
 apply outside_range_elim.
Qed.

Lemma subst_env_compat_rw:
  forall M M',
    (M ~> M') ->
    forall n env,
      (subst_env n env M ~> subst_env n env M').
Proof.
 intros M M' H.
 induction H as [ | M1 M2 N
                  | M N1 N2
                  | N N'
                  | M1 M2 N
                  | M N1 N2
                  | M1 M2 b
                  | M N
                  | M N
                  |
                  |
                  | N
                  | M
                  | M N
                  | M N
                  (* | *)
                  | M N
                  | L M N
                  | M N
                  | M
                  | b1 b2 M N
                  | b M1 M2 N
                  | b M N1 N2
                  | b M N
                  | b M N
                ];
   intros n env; simpl; eauto.

 - (* Case BetaRed *)
   apply Rw_beta; subst.
   apply commute_subst_with_beta_reduct.

 - (* Case: Beta reduction of TmBind *)
   apply Rw_Bind_beta; subst.
   apply commute_subst_with_beta_reduct.

 - (* Case: TmBind Associativity *)
   replace (subst_env (S (S n)) (map (shift 0 1) (map (shift 0 1) env)) (shift 1 1 N))
      with (shift 1 1 (subst_env (S n) (map (shift 0 1) env) N)).
   { auto. }
   rewrite shift_subst_commute_lo by lia.
   replace (S n + 1) with (S (S n)) by lia.
   rewrite 2 map_map.
   f_equal.
   apply map_ext.
   intros.
   rewrite shift_shift' by lia.
   rewrite shift_shift' by lia.
   simpl.
   auto.
 - (* Case: TmBind/TmIf commutation. *)
   replace (S n) with (n + 1) by lia.
   rewrite <- shift_subst_commute_lo by lia.
   auto.
Qed.

Lemma TmSingle_shift_inversion:
  forall x k M,
    TmSingle x = shift k 1 M -> {M' : Term & TmSingle M' = M}.
Proof.
 intros.
 destruct M; simpl in *; try discriminate.
 exists M; auto.
Qed.

Import Setoid.
Require Import Listkit.Foreach.

Lemma commute_shift_beta_reduct :
  forall k N1 N2,
    (shift (S k) 1 N1 */ shift k 1 N2) = shift k 1 (N1 */ N2).
Proof.
 intros.
 rewrite shift_unshift_commute; [ | | lia].
 { rewrite shift_subst_commute_hi by (simpl; lia).
   simpl.
   rewrite shift_shift_commute by lia.
   trivial. }
 rewrite subst_Freevars by auto.
 intro H0.
 apply set_union_elim in H0.
 destruct H0.
 - apply shift_freevars_range in H; intuition (easy).
 - apply set_filter_elim in H; intuition.
Qed.

(** If [shift k 1 N] reduces, then that reduct is equal to the
    [shift k 1] of some term which is a reduct of [N]. *)
(** Diagrammatically: [[
    N - - - -> N'
    |          :
    | f        : f = shift k 1
    |          :
    V          V
   f N ------> M
          R
]]
 *)
Lemma shift_Rw_inversion:
  forall N M k,
    (shift k 1 N ~> M) ->
    {N' : Term &  M = shift k 1 N'  &  N ~> N'}.
Proof.
(* TODO: The cases are now mostly very similar. Must be some way to automate. *)
 induction N; simpl; intros M k red; inversion red.
 - (* Case TmPair; reduction in left *)
   edestruct (IHN1 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - (* Case TmPair; reduction in right *)
   edestruct (IHN2 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - (* Case TmProj; reduction in body *)
   edestruct (IHN _ _ H2); subst.
   econstructor; eauto; simpl; eauto.

 - (* Case TmProj (left) on TmPair *)
   subst.
   descrim N (* must be pair *).
   simpl in red.
   eexists; inversion H1; auto.

 - (* Case TmProj (right) on TmPair *)
   subst.
   descrim N.
   simpl in red.
   eexists; inversion H1; auto.

 - (* Case TmAbs; reduction in body *)
   edestruct (IHN _ _ H0); subst.
   econstructor; eauto; simpl; eauto.

 - (* Case: Beta reduction. *)
   subst.
   descrim N1.
   simpl in red.
   inversion H.
   exists (N1 */ N2);
     auto using commute_shift_beta_reduct.

 - (* Case: reduction in left part of application. *)
   edestruct (IHN1 _ _ H2); subst.
   econstructor; eauto; simpl; eauto.

 - (* Case: reduction in right part of application. *)
   edestruct (IHN2 _ _ H2); subst.
   econstructor; eauto; simpl; eauto.

 - (* Case TmSingle *)
   edestruct (IHN _ _ H0); subst.
   econstructor; eauto; simpl; eauto.

 - (* Case: TmUnion, reduction in left *)
   destruct (IHN1 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - (* Case: TmUnion, reduction in right *)
   destruct (IHN2 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - (* Case: Null for Bind *)
   descrim N1.
   econstructor; eauto.

 - (* Case: Null for Bind in the body *)
   descrim N2.
   econstructor; eauto.
   auto.

 - (* Case: Beta for Bind *)
   destruct (TmSingle_shift_inversion x _ _ H); subst.
   exists (N2 */ x0); auto.
   simpl in H.
   inversion H; subst.
   apply commute_shift_beta_reduct.

 - (* Case: Bind/Union *)
   subst.
   descrim N1.
   inversion H0; subst.
   simpl in red.
   econstructor; eauto; simpl; auto.

 - (* Case: reduction in subject of TmBind. *)
   destruct (IHN1 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - (* Case: TmBind assoc *)
   subst.
   descrim N1.
   inversion H0; subst.
   exists (TmBind N1_1 (TmBind N1_2 (shift 1 1 N2))).
   simpl.
   { rewrite <- shift_shift_commute by lia; auto. }
   auto.

 - (* Case: reduction in body of TmBind. *)
   destruct (IHN2 _ _ H2); subst.
   econstructor; eauto; simpl; auto.

 - destruct (IHN1 _ _ H3); subst.
   exists (TmIf x N2 N3); auto.
 - destruct (IHN2 _ _ H3); subst.
   exists (TmIf N1 x N3); auto.
 - destruct (IHN3 _ _ H3); subst.
   exists (TmIf N1 N2 x); auto.
 - exists (TmUnion (TmIf N1 N2 TmNull) (TmIf N1 N3 TmNull)).
   simpl. auto.
   auto.
 - descrim N2.
   simpl in H1.
   inversion H1.
   exists (TmBind N2_1 (TmIf (shift 0 1 N1) N2_2 TmNull)).
   simpl.
   rewrite shift_shift_commute.
   auto.
   lia.
   descrim N3.
   auto.
Qed.

(** * Compatibility of rewriting with each of the term forms. *)

Lemma Rw_rt_Pair_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (〈 m1, n 〉) ~>> (〈 m2, n 〉).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Pair_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (〈 m, n1 〉) ~>> (〈 m, n2 〉).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_App_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (m1@n) ~>> (m2@n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_App_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (m@n1) ~>> (m@n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Proj:
  forall (b:bool) (M M' : Term), (M ~>> M') -> (TmProj b M) ~>> (TmProj b M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Abs:
  forall (M M' : Term), (M ~>> M') -> (TmAbs M) ~>> (TmAbs M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Single:
  forall (M M' : Term), (M ~>> M') -> (TmSingle M) ~>> (TmSingle M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Union_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (TmUnion m1 n) ~>> (TmUnion m2 n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Union_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (TmUnion m n1) ~>> (TmUnion m n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Bind_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (TmBind m1 n) ~>> (TmBind m2 n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Bind_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (TmBind m n1) ~>> (TmBind m n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_If_cond:
  forall b1 b2 m n : Term, (b1 ~>> b2) -> (TmIf b1 m n) ~>> (TmIf b2 m n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_If_left:
  forall b m1 m2 n : Term, (m1 ~>> m2) -> (TmIf b m1 n) ~>> (TmIf b m2 n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_If_right:
  forall b m n1 n2 : Term, (n1 ~>> n2) -> (TmIf b m n1) ~>> (TmIf b m n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Hint Resolve Rw_rt_Pair_left Rw_rt_Pair_right Rw_rt_App_left Rw_rt_App_right
     Rw_rt_Proj Rw_rt_Abs Rw_rt_Single Rw_rt_Union_left Rw_rt_Union_right
     Rw_rt_Bind_left Rw_rt_Bind_right Rw_rt_If_cond Rw_rt_If_left Rw_rt_If_right.

(** * [( */ )] and unshift. *)

Lemma beta_with_unshift_var:
  forall x M n n' k,
    n >= n' ->
    unshift n k (unshift n' 1 (subst_env n' (shift 0 1 M :: nil) (TmVar x))) =
    unshift n' 1
            (subst_env n' (shift 0 1 (unshift n k M) :: nil) (unshift (S n) k (TmVar x))).
Proof.
(* NEW *)
(*  intros. *)
(* rewrite unshift_unshift_commute by auto. *)
(* f_equal. *)
(* rewrite <- unshift_shift_commute by lia. *)
(* Search unshift. *)
(* replace (shift 0 1 M :: nil) with (map (shift 0 1) (M :: nil)) by auto. *)
(* Check subst_unshift. *)
(* rewrite <- shift_subst_commute_hi. *)

(* OLD *)
 simpl.
 intros.
 nth_error_dichotomize H1 H2 V H2; simpl in *.
  nth_error_dichotomize H3 H4 V H4; simpl in *.
   rewrite 2 Listkit.logickit.if_irrelevant.
   rewrite unshift_unshift_commute; solve [auto | lia].
  exfalso.
  assert (H0 : unshift_var (S n) k x - n' = 0) by lia.
  unfold unshift_var in H0.
  destruct (le_gt_dec (k + S n) x) in H0; solve [lia].
 nth_error_dichotomize H3 H4 W H4; simpl in *.
  exfalso.
  unfold unshift_var in H3.
  destruct (le_gt_dec (k + S n) x); solve [lia].
(* rewrite unshift_unshift_commute by lia. *)
(* rewrite unshift_shift_commute. *)
(* f_equal. *)
(* rewrite Listkit.logickit.if_cc with (f := unshift (S n) k). *)
 break; break.
    assert (x < S n) by lia.
    assert (unshift_var (S n) k x = x).
     unfold unshift_var.
     destruct (le_gt_dec (k + S n) x); solve [lia].
    replace (unshift_var (S n) k x) with x in * by auto.
    replace (x - n') with 0 in * by lia.
    simpl in *.
    inversion H2.
    inversion H4.
    rewrite unshift_unshift_commute by lia.
    rewrite unshift_shift_commute by lia.
    auto.
   exfalso.
   unfold unshift_var in g.
   destruct (le_gt_dec (k + S n) x); solve [lia].
  exfalso.
  unfold unshift_var in l.
  destruct (le_gt_dec (k + S n) x); solve [lia].
 unfold unshift, unshift_var.
 break; break; break; break; solve [lia | auto].
Qed.

Lemma beta_with_unshift:
  forall N M n n' k,
    n >= n' ->
    unshift n k (unshift n' 1 (subst_env n' (shift 0 1 M :: nil) N)) =
    unshift n' 1
            (subst_env n' (shift 0 1 (unshift n k M) :: nil) (unshift (S n) k N)).
Proof.
 induction N; intros; simpl.
 (* TmConst *)
 - auto.
 (* TmVar *)
 - apply beta_with_unshift_var; auto.
 (* TmPair *)
 - rewrite IHN1, IHN2; auto.
 (* TmProj *)
 - rewrite IHN; auto.
 (* TmAbs *)
 - rewrite IHN by lia.
   rewrite unshift_shift_commute; easy.
 (* TmApp *)
 - rewrite IHN1, IHN2; auto.
 (* TmNull *)
 - trivial.
 (* TmSingle *)
 - rewrite IHN; auto.
 (* TmUnion *)
 - rewrite IHN1, IHN2; auto.
 (* TmBind *)
 - rewrite IHN1, IHN2 by lia.
   rewrite unshift_shift_commute; easy.
 (* TmUnion *)
 - rewrite IHN1, IHN2, IHN3; auto.
 (* TmTable *)
 - auto.
Qed.

Lemma unshift_preserves_rw:
  forall M M' n k,
    (M ~> M') ->
    unshift n k M ~>
    unshift n k M'.
Proof.
 induction M; intros; inversion H; subst; simpl; eauto.

 - apply Rw_beta.
   apply beta_with_unshift.
   lia.
 - apply Rw_Bind_beta.
   apply beta_with_unshift.
   lia.
 - rewrite unshift_shift_commute by lia.
   apply Rw_Bind_assoc.
 - rewrite unshift_shift_commute by lia.
   apply Rw_If_Bind.
Qed.

Lemma shift_preserves_rw:
  forall L L' n,
    (L ~> L') ->
    shift n 1 L ~> shift n 1 L'.
Proof.
 induction L; intros; inversion H; subst; simpl; eauto.
 - apply Rw_beta.
   rewrite commute_shift_beta_reduct; auto.
 - apply Rw_Bind_beta.
   rewrite commute_shift_beta_reduct; auto.
 - rewrite shift_shift_commute by lia.
   auto.
 - rewrite shift_shift_commute by lia.
   auto.
Qed.

(* TODO: Need a better place for the below stuff, which is interactions btwn
shift/subst and rewriting. *)
Lemma shift_preserves_rw_rt:
  forall L L' n, (L ~>> L') -> shift n 1 L ~>> shift n 1 L'.
Proof.
 intros.
 induction H; subst; eauto.
 auto using Rw_rt_step, shift_preserves_rw.
Qed.

Lemma unshift_preserves_rw_rt
     : forall (M M' : Term) (n k : nat),
       (M ~>> M') -> unshift n k M ~>> unshift n k M'.
Proof.
 intros.
 induction H; subst; eauto.
 auto using Rw_rt_step, unshift_preserves_rw.
Qed.

Lemma subst_env_compat_rw_rt_var:
  forall x, forall L L' : Term,
    (L ~>> L') ->
    forall n : nat, subst_env n (L :: nil) (TmVar x) ~>> subst_env n (L' :: nil) (TmVar x).
Proof.
 simpl; intros.
 break; auto.
 destruct (x - n).
 - auto.
 - unfold nth_error; auto.
Qed.

Lemma rw_rt_in_substituend
: forall M L L' : Term,
    (L ~>> L') ->
    forall n : nat,
      subst_env n (L :: nil) M ~>> subst_env n (L' :: nil) M.
Proof.
 induction M; subst;
   try (apply subst_env_compat_rw_rt_var);
   simpl; eauto; intros.
 - eapply Rw_rt_trans; eauto.
 - eauto using Rw_rt_Abs, IHM, shift_preserves_rw_rt.
 - eapply Rw_rt_trans; eauto.
 - eapply Rw_rt_trans; eauto.
 - eapply Rw_rt_trans; eauto using IHM2, shift_preserves_rw_rt.
 - evar (X : Term).
   evar (Y : Term).
   eapply Rw_rt_trans with X; [ | eapply Rw_rt_trans with Y].
   instantiate (X :=
                  (TmIf (subst_env n (L' :: nil) M1)
                        (subst_env n (L :: nil) M2)
                        (subst_env n (L :: nil) M3))).
   subst X.
   auto.
   instantiate (Y :=
                  (TmIf (subst_env n (L' :: nil) M1)
                        (subst_env n (L' :: nil) M2)
                        (subst_env n (L :: nil) M3))).
   subst X Y.
   eauto.
   subst Y. eauto.
Qed.

Lemma subst_env_compat_rw_rt
: forall L M M' : Term,
    (M ~>> M') ->
    forall n : nat,
      subst_env n (L :: nil) M ~>> subst_env n (L :: nil) M'.
Proof.
 intros.
 induction H; subst; eauto using subst_env_compat_rw.
Qed.

Lemma subst_env_bicompat_rw_rt
: forall L L' M M' : Term,
    (L ~>> L') ->
    (M ~>> M') ->
    forall n : nat,
      subst_env n (L :: nil) M ~>> subst_env n (L' :: nil) M'.
Proof.
 intros.
 apply Rw_rt_trans with (subst_env n (L :: nil) M').
 - apply subst_env_compat_rw_rt; auto.
 - apply rw_rt_in_substituend; auto.
Qed.

(** * Rewrites Inside Structures That Look Like A Beta-Reduct. *)

Lemma unshift_substitution_preserves_rw:
  forall M M' L,
    (M ~> M') ->
    M */ L ~> M' */ L.
Proof.
 intros.
 apply unshift_preserves_rw.
 apply subst_env_compat_rw.
 auto.
Qed.

Lemma unshift_substitution_doubly_preserves_rw_rt:
  forall M M' L L' : Term,
  (L ~>> L') ->
  (M ~>> M') ->
  M */ L ~>>
    M' */ L'.
Proof.
 intros.
 apply unshift_preserves_rw_rt. (* Should be rw_compat_unshift *)
 apply subst_env_bicompat_rw_rt; auto.
 apply shift_preserves_rw_rt; auto.
Qed.
