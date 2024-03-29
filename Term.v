(*
 * Strong Normalization for Nested Relational Calculus.
 * Copyright Ezra Cooper, 2008-2020.
 *)

Require Import Arith.
Require Import List.

Add Rec LoadPath "Listkit" as Listkit.

Require Import Listkit.Foreach.

Create HintDb Term.

(** Definitions *)
Inductive Ty : Set :=
  TyBase
| TyPair : Ty -> Ty -> Ty
| TyArr : Ty -> Ty -> Ty
(* | TyAny : Ty *)
| TyList : Ty -> Ty.

(** Terms *)
Inductive Term : Set :=
  TmConst
| TmVar (x : nat) : Term
| TmPair : Term -> Term -> Term
| TmProj : bool -> Term -> Term
| TmAbs : Term -> Term
| TmApp : Term -> Term -> Term
| TmNull : Term
| TmSingle : Term -> Term
| TmUnion : Term -> Term -> Term
| TmBind : Term -> Term -> Term
| TmIf : Term -> Term -> Term -> Term
| TmTable : Ty -> Term.

Notation "L @ M" := (TmApp L M) (at level 500).
Notation "〈 L , M 〉" := (TmPair L M) (at level 400).

(** Typing derivations *)
Inductive Typing env : Term -> Ty -> Set :=
| TBase : Typing env TmConst TyBase
| TVar : forall (x:nat) ty,
    value ty = nth_error env x ->
    Typing env (TmVar x) ty
| TPair : forall l m s t, Typing env l s -> Typing env m t ->
    Typing env (TmPair l m) (TyPair s t)
| TApp : forall l m a b,
    Typing env l (TyArr a b) -> Typing env m a ->
    Typing env (TmApp l m) b
| TAbs : forall n s t,
    Typing (s :: env) n t ->
    Typing env (TmAbs n) (TyArr s t)
| TProj1 : forall m s t,
    Typing env m (TyPair s t) ->
    Typing env (TmProj false m) s
| TProj2 : forall m s t,
    Typing env m (TyPair s t) ->
    Typing env (TmProj true m) t
| TSingle : forall m t,
    Typing env m t ->
    Typing env (TmSingle m) (TyList t)
| TUnion : forall m n t,
    Typing env m (TyList t) ->
    Typing env n (TyList t) ->
    Typing env (TmUnion m n) (TyList t)
| TNull : forall t,
    Typing env TmNull (TyList t)
| TBind : forall m s n t,
    Typing env m (TyList s) ->
    Typing (s::env) n (TyList t) ->
    Typing env (TmBind m n) (TyList t)
| TTable : forall r, Typing env (TmTable r) (TyList r)
.

#[export]
Hint Constructors Typing.

(** [env_typing] relates a value environment to its typing. It asserts
    the types (in a [nil] environment) of each of a series of values. *)
Definition env_typing Vs Ts :=
  ((length Vs = length Ts) *
  foreach2_ty _ _ Vs Ts (fun x y => (Typing nil x y)))%type.

(** [env_typing_env] also relates a value environment to its typing. It asserts
    the types (in a given environment) of each of a series of values. *)
Definition env_typing_env env Vs Ts :=
  ((length Vs = length Ts) *
  foreach2_ty _ _ Vs Ts (fun x y => (Typing env x y)))%type.

#[export]
Hint Unfold env_typing.

(** [env_typing_env] environments can be extended, one term-type pair at a time. *)
Lemma env_typing_intro:
  forall env V Vs T Ts,
    Typing env V T ->
    env_typing_env env Vs Ts ->
    env_typing_env env (V::Vs) (T::Ts).
Proof.
 intros.
 unfold env_typing_env in *.
 unfold foreach2_ty in *.
 simpl in *.
 intuition.
Qed.

(** [env_typing_env] environments can be destructed into their first
pair and a remaining [env_typing_env] environment. *)
Lemma env_typing_elim:
  forall env V Vs T Ts,
    env_typing_env env (V::Vs) (T::Ts) ->
    (env_typing_env env Vs Ts
    * Typing env V T).
Proof.
 intros env V Vs T Ts X.
 unfold env_typing_env in X.
 unfold foreach2_ty in X.
 unfold env_typing_env.
 simpl in *.
 intuition.
Qed.

Lemma env_typing_cons :
  forall V T Vs env,
    Typing nil V T -> env_typing Vs env -> env_typing (V::Vs) (T::env).
Proof.
 (* Could use foreach2_ty_cons, to maintain that abstraction. *)
 intros.
 simpl;  firstorder.
 unfold foreach2_ty; simpl; intuition.
Qed.

#[export]
Hint Resolve env_typing_cons : Term.

Require Import Coq.Lists.ListSet.

Require Import Listkit.Sets.

Definition set_remove := Listkit.Sets.set_remove.

(** The free variables of a Term, as a set of nats. *)
Fixpoint freevars (M:Term) : set nat :=
  match M with
  | TmConst => empty_set nat
  | TmVar x => set_add eq_nat_dec x (empty_set nat)
  | TmPair L M => set_union eq_nat_dec (freevars L) (freevars M)
  | TmProj b M => freevars M
  | TmAbs N => set_map eq_nat_dec pred
                 (set_remove _ eq_nat_dec 0 (freevars N))
  | TmApp L M => set_union eq_nat_dec (freevars L) (freevars M)
  | TmNull => empty_set nat
  | TmSingle x => freevars x
  | TmUnion a b => set_union eq_nat_dec (freevars a) (freevars b)
  | TmBind M N => set_union eq_nat_dec (freevars M)
                            (set_map eq_nat_dec pred
                                     (set_remove _ eq_nat_dec 0 (freevars N)))
  | TmIf b M N => set_union eq_nat_dec (freevars b)
                            (set_union eq_nat_dec (freevars M) (freevars N))
  | TmTable _ => empty_set nat
  end.

Definition free_in x M := set_In x (freevars M).

Definition in_env_domain (n:nat) (env:list Term) := fun x => n <= x < n+length env.
(* (* Alt definition, reuses outside_range; consider it! *)
   Definition in_env_domain (n:nat) (env:list Term) :=
   fun x => false = outside_range n (n+length env) x. *)


(* TODO: in_env_domain and outside_range are essentially logical inverses,
   but are defined in different sorts. Consolidate them! *)

Lemma in_env_domain_map :
    forall n f env, in_env_domain n (map f env) = in_env_domain n env.
 unfold in_env_domain.
 intros.
 rewrite map_length.
 auto.
Qed.

(** A term [M] is [Neutral] if, when it reduces in context, [C[M] ~> Z], the
    reduction either in C or in M:
      C[M] ~> Z  ==  C[M] ~> C[M']  or
      C[M] ~> Z  ==  C[M] ~> C'[M].
    In other words, [M] cannot react with [C] immediately.

    But we define it here by the cases that we know have that property.
    TODO: Fix that!
 *)
Inductive Neutral : Term -> Type :=
  | Neutral_App : forall L M, Neutral (TmApp L M)
  | Neutral_Proj : forall b M, Neutral (TmProj b M)
  | Neutral_Table : forall t, Neutral (TmTable t).

#[export]
Hint Constructors Neutral.

#[export]
Hint Resolve Neutral_App.
#[export]
Hint Resolve Neutral_Proj.
