(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Load "eztactics.v".

Require Import Arith.
Require Import List.

Add Rec LoadPath "Listkit" as Listkit.

Require Import Listkit.Foreach.
Require Import Listkit.NthError.

Require Import Term.

Definition shift_var k n :=
  fun x => if le_gt_dec k x then (x + n) else x.

(** Shifting De Bruijn indexes *)
Fixpoint shift k n tm {struct tm} :=
  match tm with
| TmConst => TmConst
| TmVar x => TmVar (shift_var k n x)
(* | TmPair L M => TmPair (shift k n L) (shift k n M) *)
(* | TmProj b M => TmProj b (shift k n M) *)
| TmAbs N' => TmAbs (shift (S k) n N')
| TmApp L M => TmApp (shift k n L) (shift k n M)
(* | TmNull => TmNull *)
| TmSingle x => TmSingle (shift k n x)
(* | TmUnion L R => TmUnion (shift k n L) (shift k n R) *)
| TmBind M N => TmBind (shift k n M) (shift (S k) n N)
(* | TmIf b M N => TmIf (shift k n b) (shift k n M) (shift k n N) *)
(* | TmTable ty => TmTable ty *)
  end.

Definition unshift_var k n :=
  fun x => if le_gt_dec (n + k) x then (x - n) else x.

Fixpoint unshift k n tm {struct tm} :=
  match tm with
| TmConst => TmConst
| TmVar x => TmVar (unshift_var k n x)
(* | TmPair L M => TmPair (unshift k n L) (unshift k n M) *)
(* | TmProj b m => TmProj b (unshift k n m) *)
| TmAbs N => TmAbs (unshift (S k) n N)
| TmApp L M =>TmApp (unshift k n L) (unshift k n M)
(* | TmNull => TmNull *)
| TmSingle x => TmSingle (unshift k n x)
(* | TmUnion l r => TmUnion (unshift k n l) (unshift k n r) *)
| TmBind M N => TmBind (unshift k n M) (unshift (S k) n N)
(* | TmIf b M N => TmIf (unshift k n b) (unshift k n M) (unshift k n N) *)
(* | TmTable ty => TmTable ty *)
end.

#[local] Hint Transparent unshift_var shift_var : Shift.

Lemma unshift_var_shift_var :
  forall x k n,
    unshift_var k n (shift_var k n x) = x.
Proof.
 intros x k n.
 unfold unshift_var, shift_var.
 break; break; lia.
Qed.

Lemma unshift_shift :
  forall N k n,
    unshift k n (shift k n N) = N.
Proof.
 induction N; intros k n; simpl; f_equal; auto.
 apply unshift_var_shift_var.
Qed.

(** (Un)Shifting at De Bruijn index k when k is above the greatest free
    index is a no-op. *)
Lemma shift_nonfree_noop :
  forall n M k env T,
    length env <= k ->
    Typing env M T -> shift k n M = M.
Proof.
 induction M; simpl; intros k env T k_big M_tp; intuition;
   inversion M_tp as [| ? ? T_is_env_x | | | | | | | | | |];
     try (f_equal; eauto).
 (* Case TmVar *)
   unfold shift_var.
   break; trivial.
   pose (nth_error_to_length _ _ _ _ T_is_env_x).
   lia.
 (* Case TmAbs *)
  apply IHM with (s :: env) t; simpl; auto; lia.
 (* Case TmBind *)
 apply IHM2 with (s :: env) (TyList t); simpl; auto; lia.
Qed.

Lemma unshift_nonfree_noop :
  forall n M k env T,
    length env <= k ->
    Typing env M T -> unshift k n M = M.
Proof.
 induction M; simpl; intros k env T k_big M_tp; intuition;
   inversion M_tp as [| ? ? T_is_env_x | | | | | | | | | |];
     try (f_equal; eauto).
   unfold unshift_var.
   break; trivial.
   (* TODO: Need to parameterize efinish on hint databases? *)
   exfalso.
   apply nth_error_to_length in T_is_env_x.
   lia.
   eapply IHM with (s :: env) t; auto; simpl; lia.
 eapply IHM2 with (s :: env) (TyList t); auto; simpl; lia.
Qed.

(** (Un)Shifting a closed term is a no-op. *)
Lemma shift_closed_noop :
  forall n M k T,
    Typing nil M T -> shift k n M = M.
Proof.
 intros; eapply shift_nonfree_noop; eauto.
 simpl; apply le_O_n.
Qed.

Lemma unshift_closed_noop :
  forall n M k T,
    Typing nil M T -> unshift k n M = M.
Proof.
 intros; eapply unshift_nonfree_noop; eauto.
 simpl; apply le_O_n.
Qed.

#[export] Hint Resolve shift_closed_noop : Shift.

Lemma shift_var_nth_error:
  forall A (x:A) n env2 env1 env',
       value x = nth_error (env1 ++ env2) n
    -> value x = nth_error (env1 ++ env' ++ env2)
                           (shift_var (length env1) (length env') n).
Proof.
 unfold shift_var.
 intros ? x n env2 env1 env' H.
 destruct (le_gt_dec (length env1) n).
  assert (n < length (env1 ++ env2)) by eauto with NthError.
  rewrite app_length in H0.
  rewrite nth_error_app_eq; repeat (rewrite app_length); try finish.
  rewrite nth_error_app_eq; repeat (rewrite app_length); try finish.
  replace (n + length env' - length env1 - length env')
     with (n - length env1) by lia.
  solve [auto with NthError].
 rewrite nth_error_ext_length; auto.
 rewrite nth_error_ext_length in H by auto.
 auto.
Qed.

(** Shift preserves typing. *)
Lemma shift_preserves_typing:
  forall M k n env1 env2 env env' T,
    env1 ++ env2 = env ->
    k = length env1 ->
    n = length env' ->
    Typing env M T -> Typing (env1 ++ env' ++ env2) (shift k n M) T.
Proof.
 induction M; intros k n env1 env2 env env' T env_split k_def n_def M_tp;
   inversion M_tp as [| ? ? T_is_env_x| | | | | | | | | |]; simpl.
 (* TmConst *)
            solve [auto].
 (* TmVar *)
           subst x0 ty env n k.
           apply TVar.
           apply shift_var_nth_error; auto.
 (* (* TmPair *)
          apply TPair; eauto.
 (* TmProj *)
         eapply TProj1; eauto.
        eapply TProj2; eauto. *)
 (* TmAbs *)
       subst n0 T env k.
       apply TAbs.
       replace (s :: env1 ++ env' ++ env2)
          with ((s::env1) ++ env' ++ env2) by auto.
       eauto using IHM.
 (* TmApp *)
       eauto.
      auto.
    (* apply TSingle; eauto.
   apply TUnion; eauto. *)
 (* TmBind *)
  eapply TBind.
   eapply IHM1; seauto.
  subst env.
  replace (s :: env1 ++ env' ++ env2)
    with ((s::env1) ++ env' ++ env2) by auto.
  eapply IHM2 with (s::env1 ++ env2); auto.
  simpl.
  sauto.
  (* Case TmSingle *)
 apply TSingle.
 eapply IHM; eauto.
Qed.

(** Shifting a term by just one preserves typing. *)
Lemma shift1_preserves_typing :
  forall M env S T,
    Typing env M T -> Typing (S::env) (shift 0 1 M) T.
Proof.
 intros.
 replace (S::env) with (nil ++ (S::nil) ++ env) by trivial.
 apply shift_preserves_typing with env; auto.
Qed.

#[export] Hint Resolve shift1_preserves_typing : Shift.

(** Applying [unshift k _] to a variable _smaller_ than [k] as no effect. *)
Lemma unshift_var_lo :
  forall x k n,
    x < k -> unshift_var k n x = x.
Proof.
 simpl.
 intros x k n H.
 unfold unshift_var.
 destruct (le_gt_dec (n + k) x);
   [solve[lia]|solve[auto]].
Qed.

(** Composing one [shift] with another, at the same [k], can be
    reduced to a single [shift]. *)
Lemma shift_shift:
  forall n n' M k,
    shift k n (shift k n' M) = shift k (n + n') M.
Proof.
 induction M; intros k; simpl; try (solve [f_equal; eauto]).
(* Case TmVar *)
 f_equal.
 unfold shift_var.
 destruct (le_gt_dec k x).
  destruct (le_gt_dec k (x + n')); lia.
 destruct (le_gt_dec k x); lia.
Qed.

(** Composing one [shift] with another, where the later [k] falls in the
    gap created by the earlier [shift], can be reduced to a single [shift]. *)
Lemma shift_shift':
  forall n n' M k k',
    k' <= k -> k <= k' + n' ->
    shift k n (shift k' n' M) = shift k' (n + n') M.
Proof.
 induction M; intros k k' H0 H1; simpl; try (solve [f_equal; eauto]).
(* Case TmVar *)
 f_equal.
 unfold shift_var.
 break; break; lia.
 (* Csae TmAbs *)
 f_equal.
 apply IHM; lia.
 (* Csae TmBind *)
 f_equal.
 apply IHM1; lia.
 apply IHM2; lia.
Qed.

(** Composing [unshift] with [shift], given certain conditions (TODO)
    on the indices, produces the effect of a single [shift] *)
Lemma fancy_unshift_shift:
  forall n M k n' j,
    k + n <= j + n' ->
    j <= k ->
    unshift k n (shift j n' M) = shift j (n' - n) M.
Proof.
 induction M; intros k n' j n'_big j_small; simpl; f_equal; try eauto.
 (* Case TmVar *)
  unfold unshift_var, shift_var.
  destruct (le_gt_dec j x).
   break; lia.
  break; lia.
 (* Case TmAbs *)
  apply IHM; lia.
 (* Case TmBind *)
 apply IHM2; lia.
Qed.

Lemma shift_var_shift_var_commute:
  forall x k k' n,
    k' <= k ->
    shift_var (S k) n (shift_var k' 1 x) =
    shift_var k' 1 (shift_var k n x).
Proof.
 intros x k k' n H.
 unfold shift_var at 2 4.
 break; break.
    unfold shift, shift_var.
    break; break; lia.
   unfold shift, shift_var.
   break; break; lia.
  unfold shift, shift_var.
  break; break; lia.
 unfold shift, shift_var.
 break; break; lia.
Qed.

(** "Shifting by one" commutes with "shifting by [k]" for appropriate
   conditions and adjustment of [k]. *)
Lemma shift_shift_commute:
  forall M k k' n,
    k' <= k ->
    shift (S k) n (shift k' 1 M) =
    shift k' 1 (shift k n M).
Proof.
 induction M; intros k k' n H; try (solve [simpl; f_equal; eauto]).
 (* TmVar *)
  unfold shift at 2 4.
  unfold shift.
  f_equal.
  apply shift_var_shift_var_commute; auto.
 (* TmAbs *)
 simpl; f_equal.
 assert (S k' <= S k) by lia.
 eauto.
 simpl; f_equal.
  apply IHM1; auto.
 apply IHM2; auto.
 lia.
Qed.

Require Import Listkit.logickit.

Lemma shift_var_S_pred:
  forall x k n,
    x <> 0 ->
    pred (shift_var (S k) n x) = shift_var k n (pred x).
Proof.
 unfold shift_var.
 intros.
 pose (pred := fun x => x - 1).
 replace ((if le_gt_dec (S k) x then x + n else x) - 1)
    with (pred (if le_gt_dec (S k) x then x + n else x)) by auto.
 replace (pred (if le_gt_dec (S k) x then x + n else x))
    with (if le_gt_dec (S k) x then pred (x + n) else pred x).
  unfold pred.
  break; break; lia.
 symmetry; apply if_cc.
Qed.

Require Import Coq.Lists.ListSet.

(* TODO: grumble, why this? *)
Definition set_remove := Listkit.Sets.set_remove.

Require Import Monomorphism.
Require Import Listkit.Map.
Require Import Listkit.Sets.

Import Setoid.

Lemma not_in_union_elim: forall x A B, ~ (x ∈ A ∪ B) -> ~ (x ∈ A) /\ ~ (x ∈ B).
Proof.
  intros. split; contrapose H; apply set_union_intro; auto.
Qed.

Lemma remove_0_pred_preserves_nonzero_membership:
  forall x xs,
  (S x ∈ xs) ->
  (x ∈ set_map Nat.eq_dec Init.Nat.pred (Term.set_remove nat Nat.eq_dec 0 xs)).
Proof.
  intros.
  rewrite map_monomorphism with (f := S).
  2: { firstorder. }
  rewrite set_map_map by solve [auto with Listkit].
  apply set_map_idy_ext; [ | solve [auto with Listkit]].
  intros.
  apply set_remove_elim in H0.
  lia.
Qed.

(* TODO: The asymetry between this and shift_var_unshift_var_commute is upsetting. *)
Lemma shift_var_unshift_var_commute1:
  forall k k' x,
    x <> k' ->
    k' <= k ->
    shift_var k 1 (unshift_var k' 1 x) =
    unshift_var k' 1 (shift_var (S k) 1 x).
Proof.
  unfold not in *.
  intuition.
  unfold shift_var, unshift_var.
  break; break; break; break; lia.
Qed.

Lemma shift_unshift_commute :
  forall M k k',
    ~ set_In k' (freevars M) ->
    k' <= k ->
    shift k 1 (unshift k' 1 M) =
    unshift k' 1 (shift (S k) 1 M).
Proof.
 induction M; intros k k' k'_not_free k'_le_k; simpl in k'_not_free |- *.

 (* Case TmConst *)
          sauto.

 (* Case TmVar *)
         f_equal.
         apply shift_var_unshift_var_commute1; auto.
(* 
 (* Case TmPair *)
        rewrite IHM1, IHM2; auto with Listkit.

 (* Case TmProj *)
       f_equal; seauto. *)

 (* Case TmAbs *)
      rewrite IHM; [auto | | lia].
      contrapose k'_not_free; rename k'_not_free into S_k'_free_in_M.
      apply remove_0_pred_preserves_nonzero_membership; easy.

 (* Case TmApp *)
     rewrite IHM1, IHM2; auto with Listkit.
(* 
 (* Case TmNull *)
    sauto.

 (* Case TmUnion *)
  rewrite IHM1, IHM2; auto with Listkit. *)

 (* Case TmBind *)
 rewrite IHM1; auto with Listkit.
 rewrite IHM2; auto with Listkit; try lia.
 contrapose k'_not_free. (* TODO: contrapose should take a name for the new hypothesis. *)
 rename k'_not_free into S_k'_in_fvs_M2.
 apply set_union_intro2.
 apply remove_0_pred_preserves_nonzero_membership; easy.
(* 
 (* Case TmIf *)
 (* NB: Listkit doesn't know what to do with a three-way union, so we have to hold its hand. *)
 apply not_in_union_elim in k'_not_free.
 destruct k'_not_free.
 rewrite IHM1, IHM2, IHM3; auto with Listkit.

 (* Case TmTable *)
 sauto. *)

 (* Case TmSingle *)
 rewrite IHM; solve [auto].
Qed.

Lemma shift_up_remove_0_pred:
  forall k n xs,
    eq_sets nat
      (set_map Nat.eq_dec pred
        (set_remove nat Nat.eq_dec 0
          (set_map Nat.eq_dec (shift_var (S k) n) xs)))
      (set_map Nat.eq_dec (shift_var k n)
        (set_map Nat.eq_dec pred
          (set_remove nat Nat.eq_dec 0 xs))).
Proof.
  intros.
  replace 0 with (shift_var (S k) n 0) at 1 by solve [auto with Listkit].
  rewrite <- map_remove.
   rewrite set_map_map.
   rewrite set_map_map.
   rewrite set_map_extensionality with (g := (fun x => shift_var k n (pred x))).
    solve [auto with Listkit].
   intros.
   apply shift_var_S_pred.
   apply set_remove_elim in H; tauto.
  intros x y.
  unfold shift_var.
  break; break; lia.
Qed.

Lemma freevars_shift :
  forall M k n,
    eq_sets _
      (freevars (shift k n M))
      (set_map eq_nat_dec (shift_var k n) (freevars M)).
Proof.
 induction M; simpl; intros k n.
 (* Case TmConst *)
          solve [auto with Listkit].

 (* Case TmVar *)
          solve [auto with Listkit].
(* 
 (* Case TmPair *)
        rewrite IHM1, IHM2.
        rewrite map_union.
        solve [auto with Listkit].

 (* Case TmProj *)
       solve [eauto with Listkit]. *)

 (* Case TmAbs *)
      rewrite IHM.
      apply shift_up_remove_0_pred.

 (* Case TmApp *)
     rewrite IHM1, IHM2.
     rewrite map_union.
     solve [auto with Listkit].
(* 
 (* Case TmNull *)
    solve [trivial with Listkit].

 (* Case TmUnion *)
  rewrite IHM1, IHM2.
  rewrite map_union.
  solve [trivial with Listkit]. *)

 (* Case TmBind *)
 rewrite IHM1, IHM2.
 rewrite map_union.
 auto using shift_up_remove_0_pred with Listkit.
(* 
 (* Case TmIf *)
 rewrite IHM1, IHM2, IHM3.
 rewrite map_union.
 rewrite map_union.
 solve [trivial with Listkit].*)

 (* Case TmSingle *)
   solve [auto with Listkit].

(* (* Case TmTable *)
 solve [auto with Listkit]. *)
Qed.

Lemma pred_freevars_shift :
  forall M,
    eq_sets _
      (set_map eq_nat_dec pred (freevars (shift 0 1 M)))
      (freevars M).
Proof.
 intros.
 rewrite freevars_shift.
 rewrite set_map_map.
 apply set_map_idy_ext.
 intros.
 apply pred_shift.
Qed.

Require Import Listkit.All.

Lemma shift_var_range:
  forall x k,
    (fun x => x < k \/ k + 1 <= x) (shift_var k 1 x).
Proof.
 unfold shift_var.
 intros; break; lia.
Qed.

(* TODO: Use outside_range? *)
Lemma shift_freevars_range:
  forall M k,
    all _ (fun x => x < k \/ k + 1 <= x) (freevars (shift k 1 M)).
Proof.
 intros. rewrite freevars_shift.
 unfold all.
 intros.
 apply set_map_elim in H as [a [H1 H2]].
 subst x.
 auto using shift_var_range.
Qed.

Lemma remove_0_shift_0_1:
  forall x,
    eq_sets nat (set_remove nat eq_nat_dec 0 (freevars (shift 0 1 x)))
            (freevars (shift 0 1 x)).
Proof.
 unfold eq_sets, incl_sets.
 split; intros.
  apply set_remove_elim in H.
  tauto.
 apply set_remove_intro.
 intuition.
 apply shift_freevars_range in H.
 lia.
Qed.

Lemma unshift_var_unshift_var_commute:
  forall x k k' n,
    k' <= k ->
    unshift_var k  n (unshift_var    k' 1 x) =
    unshift_var k' 1 (unshift_var (S k) n x).
Proof.
 intros x k k' n H.
 unfold unshift_var at 2 4.
 break; break; unfold unshift_var; break; break; lia.
Qed.

Lemma unshift_unshift_commute:
  forall M k k' n,
    k' <= k ->
    unshift k n (unshift k' 1 M) =
    unshift k' 1 (unshift (S k) n M).
Proof.
 induction M; simpl; intros; try (f_equal; auto).
 - rewrite unshift_var_unshift_var_commute; sauto.
 - apply IHM.
   lia.
 - apply IHM2.
   lia.
Qed.

Lemma shift_var_unshift_var_commute:
  forall x k k' n,
    k' <= k ->
    unshift_var (S k) n (shift_var  k' 1 x) =
    shift_var      k' 1 (unshift_var k n x).
Proof.
 intros x k k' n H.
 unfold unshift_var, shift_var.
 break; break; break; break; lia.
Qed.

Lemma unshift_shift_commute:
  forall M k k' n,
    k' <= k ->
    unshift (S k) n (shift k' 1 M) =
    shift k' 1 (unshift k n M).
Proof.
 induction M; simpl; intros; try (f_equal; auto).
 - rewrite shift_var_unshift_var_commute; sauto.
 - apply IHM.
   lia.
 - apply IHM2.
   lia.
Qed.

Lemma shift_closed_noop_map:
  forall n k vs ts,
    env_typing vs ts
    -> map (shift n k) vs = vs.
Proof.
 induction vs as [|a vs]; simpl; intros.
  auto.
 destruct ts; simpl in *; try (destruct H; discriminate).
 apply env_typing_elim in H.
 destruct H.
 f_equal.
 - erewrite shift_closed_noop; eauto.
 - eauto.
Qed.

#[export] Hint Resolve shift_closed_noop_map : Shift.
