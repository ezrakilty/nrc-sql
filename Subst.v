(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Load "eztactics.v".

Require Import Arith.
Require Import List.

Add LoadPath "Listkit" as Listkit.

Require Import Listkit.AllType.
Require Import Listkit.AllType.
Require Import Listkit.Foreach.
Require Import Listkit.Map.
Require Import Listkit.NthError.
Require Import Listkit.Sets.
Require Import Listkit.listkit.

Require Import OutsideRange.
Require Import Shift.
Require Import Term.
Require Import Typing.

Hint Rewrite map_length: map.

(*Section Subst.*)

(** Until I did all this, I didn't realize that substitution was a big
ask; a complex function with an algorithm in its own right. *)

Ltac map_lia :=
   autorewrite with map; lia.

(** * Simultaneous substitution of a list of terms beginning at De Bruijn index k *)
Fixpoint subst_env k vs tm {struct tm} :=
  match tm with
  | TmConst => tm
  | TmVar x =>
    if le_gt_dec k x then
      match nth_error vs (x - k) with
      | None => tm
      | Some v => v
      end
    else tm
  | TmPair l m => TmPair (subst_env k vs l) (subst_env k vs m)
  | TmProj b m => TmProj b (subst_env k vs m)
  | TmApp l m => TmApp (subst_env k vs l) (subst_env k vs m)
  | TmAbs n => TmAbs (subst_env (S k) (map (shift 0 1) vs) n)
  | TmNull => TmNull
  | TmSingle m => TmSingle (subst_env k vs m)
  | TmUnion m n => TmUnion (subst_env k vs m) (subst_env k vs n)
  | TmBind m K => TmBind (subst_env k vs m) (subst_env (S k) (map (shift 0 1) vs) K)
  | TmIf b m n => TmIf (subst_env k vs b) (subst_env k vs m) (subst_env k vs n)
  | TmTable ty => tm
  end.

Ltac break_ne :=
  match goal with
  | |- context C [nth_error (map ?f ?A) ?B]
  => rewrite nth_error_map
  | H: nth_error ?A ?B = ?C |- context C [nth_error ?A ?B]
  => rewrite H
  | |- context C [match nth_error ?A ?B with _ => _ end]
        => let a := fresh "a" in
           let b := fresh "b" in
           let c := fresh "c" in
           let d := fresh "d" in
              nth_error_dichotomize a b c d (* bounds is_error v v_def *)
        end.

(* This "magic" tactic is quite likely to solve goals involing subst_env. *)
Ltac magic :=
  (repeat double_case; simpl);
  (repeat (rewrite nth_error_map); simpl);
  (repeat breakauto; simpl);
  (repeat (rewrite nth_error_map); simpl);
  (repeat break_ne; simpl);
  try solve [auto | lia].

Lemma subst_env_nonfree_noop:
  forall N T env Vs n,
    Typing env N T ->
    n >= length env ->
      subst_env n Vs N = N.
Proof.
 induction N; simpl; intros T env Vs n tp n_big;
   auto; inversion tp; try (f_equal; eauto).
 (* Case TmVar *)
  break; [ | sauto].
  subst.
  case_eq (nth_error Vs (x - n)); [ | sauto].
  absurd (x < length env).
    efinish.
   efinish_new NthError.
 (* Case TmAbs *)
 eapply IHN; efinish.
 (* Case TmBind *)
 eapply IHN2 with (T:=TyList t).
  apply H3.
 simpl; lia.
Qed.

Lemma subst_env_closed_noop:
  forall N T Vs n,
    Typing nil N T ->
      subst_env n Vs N = N.
Proof.
 intros.
 eapply subst_env_nonfree_noop; eauto.
 simpl; lia.
Qed.

    (* env_typing Vs env' -> *)
    (* x < length Vs & x < length env' & Typing (TmVar x) T *)
Lemma subst_env_preserves_typing_var:
  forall x Vs env env' T k,
    env_typing Vs env' ->
    Typing (env ++ env') (TmVar x) T ->
    k = length env ->
      Typing env (subst_env k Vs (TmVar x)) T.
Proof.
 simpl; intros x Vs env env' T k Vs_tp tp k_eq; inversion tp; subst.
 destruct Vs_tp as [Vs_env'_equilong Vs_tp].
 destruct (le_gt_dec (length env) x).
 - (* Case x is beyond [length env] *)
   case_eq (nth_error Vs (x - length env));
     [intros v H_v | intros H_v]; auto.
   (* Obtained value v for x - length env in Vs. *)
    apply Weakening_closed.
    eapply foreach2_ty_member; eauto.
    auto with NthError.
   (* Bogus case of no value for x - length env. *)
   refute.
   apply nth_error_ok_rev in H0.
   apply <- nth_error_overflow in H_v.
   rewrite app_length in H0.
   lia.
 - (* Case of x in env. *)
  apply TVar.
  rewrite nth_error_ext_length in H0; auto.
Qed.

(**
       Vs :: env'
env, env' |- M       : T
env       |- M{Vs/k} : T    (where k = length env)
*)
Lemma subst_env_preserves_typing:
  forall M Vs env env' T k,
    env_typing Vs env' ->
    Typing (env ++ env') M T ->
    k = length env ->
      Typing env (subst_env k Vs M) T.
Proof.
 induction M; simpl; intros Vs env env' T k Vs_tp tp k_eq;
    inversion tp; subst; eauto.
 - (* Case TmVar *)
   eapply subst_env_preserves_typing_var; eauto.
 - (* Case TmAbs *)
   apply TAbs.
   replace (S (length env)) with (length (s::env)) by trivial.
   apply IHM with env'; trivial.
   erewrite env_typing_shift_noop; eauto.
 - (* Case TmBind *)
   eapply TBind; eauto using IHM1, IHM2.
   erewrite env_typing_shift_noop; eauto.
Qed.

(* Note: Used only in one place, in sn.v! *)
#[export] Hint Resolve subst_env_preserves_typing : Subst.

Lemma subst_nil :
  forall N k, subst_env k nil N = N.
Proof.
 induction N; intros k; simpl; try (solve [f_equal; eauto]).
 (* Case TmVar *)
 rewrite nth_error_nil.
 destruct (le_gt_dec k x); auto.
Qed.

(** If a variable is bigger than [q + length env] then it is untouched
 by substituting ([q], [env]). *)
(* TODO: This might be a lemma that would be immediate from a lemma about
   subst_env and freevars. *)
Lemma subst_env_big_var :
  forall q x env,
    q + length env <= x ->
      subst_env q env (TmVar x) = TmVar x.
Proof.
 intros.
 simpl.
 break; auto.
 nth_error_dichotomize bounds is_error v v_def; auto.
 finish.
Qed.

Lemma shift_subst_commute_hi_var:
  forall (x : nat) (env : list Term) (k q n : nat),
    q + length env <= k ->
    shift k n (subst_env q env (TmVar x)) =
    subst_env q (map (shift k n) env) (shift k n (TmVar x)).
Proof.
  intros.
  unfold shift at 3.
  unfold shift_var.
  destruct (le_gt_dec k x) ; [ | ].
   rewrite subst_env_big_var by lia.
   rewrite subst_env_big_var.
    simpl; unfold shift_var.
    break; finish.
   solve[map_lia].
  repeat (magic; unfold shift_var; simpl).
Qed.

Lemma shift_subst_commute_helper:
  forall M env k q n,
    subst_env q (map (shift (S k) n) (map (shift 0 1) env)) M =
    subst_env q (map (shift 0 1)     (map (shift k n) env)) M.
Proof.
  intros.
  f_equal.
  repeat (rewrite map_map).
  apply map_ext; intros x.
  apply shift_shift_commute.
  lia.
Qed.

Lemma shift_subst_commute_hi:
  forall M env k q n,
    q + length env <= k ->
    shift k n (subst_env q env M) =
      subst_env q (map (shift k n) env) (shift k n M).
Proof.
 induction M; intros env k q n k_overbounds_subst; simpl; try (f_equal; eauto).

 (* Case TmVar *)
- apply shift_subst_commute_hi_var; auto.

 (* Case TmAbs *)
 - rewrite IHM by map_lia.
   apply shift_subst_commute_helper.

 (* Case TmBind *)
 - rewrite IHM2 by map_lia.
   apply shift_subst_commute_helper.
Qed.

Lemma shift_subst_commute_lo:
  forall M env k q n,
    k <= q ->
    shift k n (subst_env q env M) =
      subst_env (q + n) (map (shift k n) env) (shift k n M).
Proof.
 induction M; simpl; intros env k q n k_low; try (f_equal; eauto).
 (* TmVar *)
        unfold shift_var.
        (* Take cases on where x is in relation to k, q: *)
        case_eq (le_gt_dec q x); intros;
          case_eq (le_gt_dec k x); intros; try (solve[exfalso;lia]);
          destruct (le_gt_dec (q + n) (x + n)); try (solve[exfalso;lia]).
        (* Case k <= q <= x. *)
          replace (x + n - (q + n)) with (x - q) by lia.
          (* Take cases on whether x - q is defined in env: *)
          nth_error_dichotomize index_hi result_none V V_def;
            rewrite nth_error_map ; (rewrite result_none || rewrite V_def);
          simpl; unfold shift_var.
          (* Case length env <= x - q. *)
           rewrite H0; sauto.
          (* Case x - q < length env. *)
          sauto.
        (* Case k <= x < q. *)
         simpl; unfold shift_var.
         solve [breakauto].
        (* Case x < k <= q. *)
        breakauto.
        simpl; unfold shift_var.
        rewrite H0; sauto.

 (* Case TmAbs *)
     rewrite IHM by lia.
     apply shift_subst_commute_helper.

 (* Case TmBind *)
 rewrite IHM2 by lia.
 apply shift_subst_commute_helper.
Qed.

(** If two successive substitutions are "independent" and adjacent then we can combine
   them into one (on a var). *)
Lemma subst_env_concat_TmVar:
  forall (x : nat) (Vs Ws : list Term) (env : list Ty) (k : nat),
    env_typing (Vs ++ Ws) env ->
    length (Vs ++ Ws) = length env ->
       subst_env k Vs (subst_env (k + length Vs) Ws (TmVar x)) =
       subst_env k (Vs ++ Ws) (TmVar x).
Proof.
 intros ? ? ? ? ? env_closed VsWs_env_equilong.
 unfold subst_env at 3.
 unfold subst_env at 2.
 unfold env_typing in *.

 case_eq (le_gt_dec k x); [intros k_le_x ?|intros x_gt_x H].
 (* Case k <= x *)
  replace (x - (k + length Vs)) with (x - k - length Vs) by lia.

  destruct (equilong_nth_error Term Ty (Vs ++ Ws) env (x - k))
        as [[x_small [VW' [T' HH]]] | [x_large HH]]; trivial;
    destruct HH as [lookup_VWs lookup_env].
  (* Case x < k + length (Vs ++ Ws) *)
   destruct (le_gt_dec (k + length Vs) x).
   (* Case k + length Vs <= x *)
    rewrite <- rewrite_nth_error_app; [|lia].
    rewrite lookup_VWs; simpl.
    (* subst_env k Vs VW' = VW': *)
    apply subst_env_closed_noop with T'.
    (* Typing nil VW' T': *)
    eapply foreach2_ty_member; eauto.
    apply env_closed.
   (* Case k + length Vs > x *)
   simpl; rewrite H.
   (rewrite nth_error_ext_length in lookup_VWs by lia);
   (rewrite nth_error_ext_length by lia; reflexivity).

  (* Case x >= k + length (Vs ++ Ws) *)
  rewrite app_length in x_large.
  rewrite <- rewrite_nth_error_app; [|lia].
  rewrite lookup_VWs; simpl.
  double_case.
  apply subst_env_big_var; lia.

 (* Case k > x *)
 break; [exfalso; lia| ].
 simpl.
 rewrite H; easy.
Qed.

(** If two successive substitutions are "independent" and adjacent then we can combine
   them into one. *)
Lemma subst_env_concat:
  forall N Vs Ws env k,
    env_typing (Vs ++ Ws) env->
    let k' := k + length Vs in
    let VWs := Vs ++ Ws in
      subst_env k Vs (subst_env k' Ws N) = subst_env k (VWs) N.
Proof.
 let triage := solve[simpl; f_equal; eauto] in
 induction N; intros Vs Ws env k env_closed;
     inversion env_closed as [VsWs_env_equilong env_closed'];
     trivial; try triage.

 (* Case TmVar *)
  eapply subst_env_concat_TmVar; eauto.

 (* Case TmAbs *)
  simpl; f_equal.
  rewrite map_app.
  replace (length Vs) with (length (map (shift 0 1) Vs)); [|apply map_length].
  replace (S (k + length (map (shift 0 1) Vs))) with
     (S k + length (map (shift 0 1) Vs)); [|easy].
  apply IHN with env; auto.
  rewrite <- map_app.
  erewrite env_typing_shift_noop; eauto.

 (* Case TmBind *)
 simpl; f_equal; eauto.
 rewrite map_app.
 replace (length Vs) with (length (map (shift 0 1) Vs)); [|apply map_length].
 replace (S(k + length (map (shift 0 1) Vs))) with
    (S k + length (map (shift 0 1) Vs)); [|easy].
 apply IHN2 with env; auto.
 rewrite <- map_app.
 erewrite env_typing_shift_noop; eauto.
Qed.

(** Shifting creates a term with a "dummy" (unused) variable;
    substituting at that variable has no effect, so we can drop it off
    the environment for substitution. *)
Lemma subst_dummyvar :
  forall N h t k,
    subst_env k (h::t) (shift k 1 N) = subst_env (S k) t (shift k 1 N).
Proof.
 induction N; intros h t1 k; try (solve[simpl; f_equal; eauto]).
 (* TmVar *)
 unfold shift, shift_var.
 destruct (le_gt_dec k x).
  unfold subst_env.
  replace (x + 1 - k) with (S (x - k)) by lia.
  replace (nth_error (h::t1) (S (x - k))) with (nth_error t1 (x - k)) by auto.
  replace (x + 1 - (S k)) with (x - k) by lia.
  repeat breakauto.
 unfold subst_env.
 repeat breakauto.
Qed.

Lemma subst_var_outside_range:
  forall q env x,
    outside_range q (length env + q) x = true ->
      subst_env q env (TmVar x) = TmVar x.
Proof.
 unfold outside_range.
 intros.
 simpl.
 magic.
 break_in H; lia. (* Maybe break should explore hypotheses anyway? *)
Qed.

Lemma subst_var_inside_range:
  forall q env x,
    outside_range q (length env + q) x = false ->
      exists X, value X = nth_error env (x - q) /\
                (subst_env q env (TmVar x)) = X.
Proof.
 unfold outside_range.
 intros.
 simpl.
 break_in H. (* If break_in were done in magic, whole proof would be automated. *)
 - magic.
   * break_in H; easy.
   * eauto.
 - easy.
Qed.

Definition set_remove := Listkit.Sets.set_remove.

(** [unshift q k] commutes with subst, if we offset the environment by
    [k] and [shift q k] all its terms.

    TODO: Consider making this use outside_range.
*)
Lemma subst_unshift :
  forall M env q k n,
    q <= n ->
    all_Type _ eq_nat_dec (fun x => Outside_Range q (k + q) x) (freevars M) ->
      subst_env n env (unshift q k M) =
      unshift q k (subst_env (n + k) (map (shift q k) env) M).
Proof.
 induction M; simpl; intros env q k n q_le_n fvs_dichot;
   try (apply all_Type_union_rev in fvs_dichot; destruct fvs_dichot);
   try (f_equal; eauto).
 (* Case TmVar *)
     assert (H : {x < q} + {x >= k + q}).
      unfold all_Type in fvs_dichot.
      apply fvs_dichot.
      simpl.
      auto.
     unfold unshift, shift, unshift_var, shift_var.
     simpl.
     rewrite nth_error_map.
     replace (x - (n + k)) with (x - k - n) by lia.

     destruct H.
     (* x < q *)
      break; break; break; try break; finish.
     (* x >= k + q *)
     destruct (le_gt_dec (k + q) x); [ | finish].
     destruct (le_gt_dec n (x - k)).
      destruct (le_gt_dec (n + k) x); [ | finish].
      nth_error_dichotomize bounds is_error v v_def.
       break; finish.
      rewrite unshift_shift; auto.
     destruct (le_gt_dec (n + k) x); [ finish | ].
     break; finish.

 (* Case TmAbs *)
  simpl in *.
  rewrite map_map.
  replace (map (fun x => shift 0 1 (shift q k x)) env)
     with (map (fun x => shift (S q) k (shift 0 1 x)) env)
       by (apply map_ext ; intro M'; apply shift_shift_commute; solve [auto|lia]).
  rewrite IHM.
    rewrite -> map_map; solve [trivial].
   solve [lia].

  (* Obligation: that if {x - 1 | x \in (S \\ {0})} is all outside [q, k + q),
     then {x | x \in S} is all outside [Sq, k + Sq). *)
  clear IHM.
  unfold all_Type in *.
  intros x H.
  destruct x.
   unfold Outside_Range.
   left; lia.
  specialize (fvs_dichot x).
  lapply fvs_dichot.
  unfold Outside_Range; firstorder lia.
  replace x with (pred (S x)) by lia.
  apply set_map_intro.
  solve [auto with Listkit].

 (* Case TmBind *)
 rewrite IHM2; (try lia || auto).
  f_equal.
  apply shift_subst_commute_helper.
 apply all_Type_map_fwd in a0.
 unfold all_Type.
 unfold all_Type in a0.
 intros.
 unfold Term.set_remove in a0.
 destruct (eq_nat_dec x 0).
  subst x.
  unfold Outside_Range.
  left; lia.
 specialize (a0 x).
 lapply a0.
  unfold Outside_Range.
  intros H0.
  destruct H0.
   left; lia.
  right; lia.
 apply set_remove_intro.
 intuition.

 (* Case TmIf *)
 apply all_Type_union_rev in a0 as [a0 a1].
 rewrite (IHM2 _ _ _ _); auto.
 apply all_Type_union_rev in a0 as [a0 a1].
 rewrite (IHM3 _ _ _ _); auto.
Qed.

Import Setoid.

Lemma union_distrib: forall A B C, eq_sets _ (A ∪ (B ∪ C)) ((A ∪ B) ∪ (A ∪ C)).
Proof.
 intros.
 split; solve_set_union_inclusion.
Qed.

(* Notation "{ q / env } M" := (subst_env q env M) (at level 100). *)
Notation "A ⊆ B" := (incl_sets nat A B) (at level 100).
Notation "A % x" := (Term.set_remove nat eq_nat_dec x A) (at level 100).

Lemma subst_freevars_binder:
 forall M env q,
 set_map Nat.eq_dec Init.Nat.pred
   ((set_unions nat Nat.eq_dec (map freevars (map (shift 0 1) env))
     ∪ set_filter nat
         (fun x : nat =>
          outside_range (S q) (length (map (shift 0 1) env) + S q) x)
         (freevars M)) % 0)
 ⊆ (set_unions nat Nat.eq_dec (map freevars env)
    ∪ set_filter nat (fun x : nat => outside_range q (length env + q) x)
        (set_map Nat.eq_dec Init.Nat.pred (freevars M % 0))).
Proof.
 intros M env q.

 (* consider that this works as well as the explicit rewrites below :-/ *)
 (* Hint Rewrite map_length map_map set_filter_map union_remove unions_remove map_union set_unions_map : idunno. *)
 (* autorewrite with idunno. *)

 rewrite map_length.
 rewrite map_map.
 rewrite set_filter_map.
 rewrite union_remove.
 rewrite unions_remove.
 rewrite map_map.
 rewrite map_union.
 rewrite set_unions_map.
 rewrite map_map.

 (* Corresponding sides of the union are \subseteq *)

 apply incl_sets_union.
 (* Left side *)
  rewrite <- filter_remove.
  set (f := fun x : nat => outside_range (S q) (length env + S q) x).
  set (g := fun x : nat => outside_range q (length env + q) (pred x)).
  rewrite filter_extensionality with (g:=g); [solve [auto with Listkit]|].
  intros.
  assert (x <> 0).
   apply set_remove_elim in H.
   intuition.
  unfold f, g.
  unfold outside_range.
  break; break; try (break; try break); auto; finish.
 (* Right side *)
 apply unions2_mor.
 apply compwise_eq_sets_map.
 intros x.
 setoid_replace (set_remove nat eq_nat_dec 0 (freevars (shift 0 1 x)))
        with (freevars (shift 0 1 x)).
 rewrite pred_freevars_shift; solve [auto with Listkit].
 solve[apply remove_0_shift_0_1].
Qed.

(** After making a substitution, the freevars of the result is:
     - the freevars of the original term,
     - less the range of variables we replaced
     - union the freevars of all the substituted terms.
 *)
Lemma subst_Freevars:
  forall M env q,
    incl_sets _
      (freevars (subst_env q env M))
      (set_union eq_nat_dec
        (set_unions nat eq_nat_dec (map freevars env))
        (set_filter nat (fun x => outside_range q (length env + q) x) (freevars M))).
Proof.
 induction M; intros env q.
 (* Case TmConst *)
            simpl; solve [auto with Listkit].

 (* Case TmVar *)
           case_eq (outside_range q (length env + q) x); intro H.
           (* Case x is outside [q, k + q). *)
            rewrite subst_var_outside_range by trivial.
           simpl.
           rewrite H.
           apply incl_sets_union2.

           (* Case x is inside [q, k + q). *)
           destruct (subst_var_inside_range q env x H) as [M [H0 H1]].
           rewrite H1.
           apply incl_union_left.
           apply nth_error_set_unions with (n := x - q).
           rewrite nth_error_map.
           rewrite <- H0.
           sauto...

 (* Case TmPair *)
          simpl.
          rewrite IHM1 by auto.
          rewrite IHM2 by auto.
          rewrite set_filter_union.
          solve_set_union_inclusion. (* TODO: Make this opaque-ify anything that doesn't contain
                                           set_union *)

 (* Case TmProj *)
         simpl.
         apply IHM; auto.

 (* Case TmAbs *)
        simpl.
        rewrite IHM by auto.
        clear IHM.
        apply subst_freevars_binder; auto.

 (* Case TmApp *)
       simpl.
       rewrite IHM1 by auto.
       rewrite IHM2 by auto.
       setoid_rewrite set_filter_union.
       solve_set_union_inclusion.

 (* Case TmNull*)
      simpl.
      solve [auto with Listkit].

 (* Case TmSingle*)
     simpl.
     rewrite IHM.
     solve [auto with Listkit].

 (* Case TmUnion*)
    simpl.
    rewrite IHM1 by auto.
    rewrite IHM2 by auto.
    rewrite set_filter_union.
    solve_set_union_inclusion.

 (* Case TmBind *)
   simpl.
   rewrite IHM1 by auto.
   rewrite set_union_assoc.
   rewrite set_filter_union.

   rewrite <- set_union_assoc.
   remember (set_unions nat eq_nat_dec (map freevars env)).
   remember (set_filter nat (fun x : nat => outside_range q (length env + q) x)
            (freevars M1)).
   remember (set_filter nat (fun x : nat => outside_range q (length env + q) x)
              (set_map eq_nat_dec pred (freevars M2 % 0))).
   setoid_replace (s ∪ (l ∪ l0)) with ((s ∪ l) ∪ (s ∪ l0)) by (apply union_distrib).

   apply incl_sets_union; [| solve [auto with Listkit]].
   subst s l l0.

   rewrite IHM2.
   simpl.
   apply subst_freevars_binder.

 (* Case TmIf *)
  simpl.
  rewrite IHM1, IHM2, IHM3 by auto.
  rewrite set_filter_union.
  rewrite set_filter_union.
  solve_set_union_inclusion.

 (* Case TmTable *)
 simpl.
 solve [auto with Listkit].
Qed.

Lemma subst_unused_noop:
  forall M env n,
    all nat (fun x => not (in_env_domain n env x)) (freevars M)
    -> subst_env n env M = M.
Proof.
 induction M; simpl; intros; try (
   try (rewrite all_union in H; destruct H);
   f_equal; auto
 ).
 (* Case TmVar *)
   assert (~in_env_domain n env x).
    unfold all in H.
    apply H.
    unfold set_In, In.
    auto.
   unfold in_env_domain in H0.
   break; auto.
   nth_error_dichotomize bounds is_error v v_def; finish.
 (* Case TmAbs *)
  rewrite IHM; [auto|].
  unfold all.
  unfold all in H.
  intros.
  cut (~in_env_domain (S n) env x).
   unfold in_env_domain.
   rewrite map_length.
   auto.
  destruct (eq_nat_dec x 0).
   unfold in_env_domain.
   lia.
  cut (~in_env_domain n env (pred x)).
   unfold in_env_domain.
   intros.
   lia.
  apply H.
  apply set_map_intro.
  apply set_remove_intro.
  auto.

 (* Case TmBind *)
  rewrite IHM2.
   auto.
  apply all_map in H0.
 rewrite in_env_domain_map.
 unfold all in H0 |- *.
 intros x H1.
 destruct (eq_nat_dec x 0).
  unfold in_env_domain.
  lia.
 set (H2 := H0 x).
 lapply H2.
  unfold in_env_domain.
  lia.
 apply set_remove_intro.
 auto.

 (* Case TmIf *)
 apply all_union in H0; destruct H0.
 auto.
 apply all_union in H0; destruct H0.
 auto.
Qed.

Lemma subst_factor_binder:
  forall N m n env env',
  (forall (m n : nat) (env : set Term) (env' : list Term),
      all Term
        (fun z : Term =>
         all nat (fun x : nat => ~ in_env_domain m env' x) (freevars z)) env ->
      m + length env' <= n \/ n + length env <= m ->
      subst_env m (map (subst_env n env) env') (subst_env n env N) =
      subst_env n env (subst_env m env' N)) ->
  all Term
       (fun z : Term =>
        all nat (fun x : nat => ~ in_env_domain m env' x) (freevars z)) env ->
  m + length env' <= n \/ n + length env <= m ->
  subst_env (S m) (map (shift 0 1) (map (subst_env n env) env'))
    (subst_env (S n) (map (shift 0 1) env) N) =
  subst_env (S n) (map (shift 0 1) env)
    (subst_env (S m) (map (shift 0 1) env') N).
Proof.
 intros N m n env env' IHN H0 H1.
 replace (S m) with (m + 1) by lia.
 replace (S n) with (n + 1) by lia.
 rewrite map_map.
 rewrite map_ext with (g:=(fun x => subst_env (n + 1) (map (shift 0 1) env) (shift 0 1 x))).
  replace (map (fun x : Term => subst_env (n + 1) (map (shift 0 1) env) (shift 0 1 x)) env')
     with (map (subst_env (n + 1) (map (shift 0 1) env)) (map (shift 0 1) env')).
   apply IHN.

    (* Preservation of the free-variable relationship. *)
    unfold (*all_terms,*) all in H0 |- *.
    intros Z Z_source x x_free_in_Z.
    destruct (map_image _ _ (shift 0 1) Z env Z_source) as [X' [X_X'_eq X'_in_env]].
    pose (n0 := H0 X' X'_in_env (pred x)).
    subst Z.
    unfold in_env_domain in *.
    rewrite map_length.
    lapply n0.
     lia.
    apply freevars_shift in x_free_in_Z.
    apply set_map_image in x_free_in_Z.
    destruct x_free_in_Z as [x' [x'_def x'_in_X'_fvs]].
    subst x.
    replace (pred (shift_var 0 1 x')) with (x'); auto.
    unfold shift_var. break; lia.
   solve[map_lia].
  rewrite map_map; solve [trivial]...
 intro.
 rewrite shift_subst_commute_lo; [auto|].
 solve [lia]...
Qed.

Lemma subst_factor_var:
 forall x m n env env',
 (* If *)
 (* 1. All freevars of all items in env are not in the domain of env', *)
 all _ (fun z =>
            all _ (fun x => not (in_env_domain m env' x)) (freevars z)) env ->
 (* 2. and the domain (m,env') does not contain n, and (n,env) does not contain m,
    i.e. they are nonoverlapping: *)
 (m + length env' <= n \/ n + length env <= m) ->
 (* Then *)
 (* We can "commute" the two substitutions, with a modification to one: *)
   subst_env m (map (subst_env n env) env') (subst_env n env (TmVar x)) =
   subst_env n env (subst_env m env' (TmVar x)).
Proof.
  simpl.
  intros x m n env env' H0 H1.
(* Either we are in the range of [n x env] or we are in the range of
  [m x env'] or neither--since they don't overlap. *)
  set (P := m <= x < m + length env').
  set (Q := n <= x < n + length env).

  assert (H : not P /\ Q \/ P /\ not Q \/ not P /\ not Q).
  subst P Q.

  intuition.
    destruct (le_gt_dec x n);
      destruct (le_gt_dec x m);
      lia.
  destruct (le_gt_dec x n);
    destruct (le_gt_dec x m);
    lia.

  destruct H as [H | [H | H]].
  (* x is in the (n, env) range and not in (m, env') *)
  - destruct H; subst P Q.
    assert (H3: x - n < length env) by lia.
    destruct (nth_error_exists _ env (x - n) H3)
      as [v v_def].
    pose (v_fvs_notin_m_env' := nth_error_all _ _ _ _ _ v_def H0).
    clearbody v_fvs_notin_m_env'.

    assert (v_subst_env'_noop: forall f, subst_env m (map f env') v = v).
    { intro f.
      apply subst_unused_noop.
      rewrite in_env_domain_map.
      auto.
    }

    repeat magic.

  (* x is in the (m, env') range and not in (n, env) *)
  - destruct H; subst P Q.
    repeat magic.

  (* x is in the (m, env') range and not in (n, env) *)
  - destruct H; subst P Q.
    repeat magic.
Qed.

Lemma subst_factor :
  forall N m n env env',
    (* If *)
    (* 1. All freevars of all items in env are not in the domain of env', *)
    all _ (fun z =>
                all _ (fun x => not (in_env_domain m env' x)) (freevars z)) env ->
    (* 2. and the domain (m,env') does not contain n, and (n,env) does not contain m,
       i.e. they are nonoverlapping: *)
    (m + length env' <= n \/ n + length env <= m) ->
    (* Then *)
    (* We can "commute" the two substitutions, with a modification to one: *)
      subst_env m (map (subst_env n env) env') (subst_env n env N) =
      subst_env n env (subst_env m env' N).
(* TODO: reverse the orientation of that equation. *)
Proof.
 induction N; intros m n env env' H0 H1; simpl; try (solve[f_equal; auto using subst_factor_binder]).
 (* Case TmVar *)
 - apply subst_factor_var; auto.
 Qed.

(* Some notations might be nice, but I'm not sure I've got the right ones yet.

(*
Notation "N { M / x }" := (subst_env x (M :: nil) N) (at level 900). *)
Notation "{ x / env } N" := (subst_env x env N) (at level 100).
Notation "{ x :/ M } N" := (subst_env x (M :: nil) N) (at level 100).

Notation "^^ M" := (shift 0 1 M) (at level 98).
Notation ",, M" := (unshift 0 1 M) (at level 98).
*)

Lemma closing_subst_closes:
  forall vs ts m t,
    env_typing vs ts ->
    Typing ts m t ->
    Typing nil (subst_env 0 vs m) t.
Proof.
 intros.
 apply subst_env_preserves_typing with (env' := ts); simpl; auto.
Qed.

(*End Subst.*)
