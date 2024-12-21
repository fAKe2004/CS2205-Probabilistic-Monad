Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope list.

(* Adds on *)
Require Import Classical.

Theorem equiv_in_domain:
  forall {A B: Type} (f: A -> B) (R: B -> B -> Prop),
    Equivalence R ->
    Equivalence (fun a1 a2 => R (f a1) (f a2)).
Proof.
  intros.
  split.
  + unfold Reflexive.
    intros.
    reflexivity.
  + unfold Symmetric.
    intros.
    symmetry; tauto.
  + unfold Transitive.
    intros.
    transitivity (f y); tauto.
Qed.

(*********************************************************)
(**                                                      *)
(** General Definition of Monad                          *)
(**                                                      *)
(*********************************************************)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity) : monad_scope.

End MonadNotation.

Arguments bind: simpl never.
Arguments ret: simpl never.
Import MonadNotation.
Local Open Scope monad.

(*********************************************************)
(**                                                      *)
(** Set Monad                                            *)
(**                                                      *)
(*********************************************************)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => eq a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

Definition Hoare {A: Type} (c: SetMonad.M A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.

#[export] Instance SetMonad_bind_congr (A B: Type):
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b; split; intros [a ?]; exists a.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
Qed.

#[export] Instance Hoare_congr {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Proof.
  unfold Proper, respectful.
  intros; unfold Hoare.
  subst.
  split; intros.
  + rewrite <- H in H1.
    apply (H0 a); tauto.
  + rewrite H in H1.
    apply (H0 a); tauto.
Qed.

(*********************************************************)
(**                                                      *)
(** Probability Distribution                             *)
(**                                                      *)
(*********************************************************)

Definition sum (l: list R): R :=
  fold_right Rplus 0%R l.

Definition sum_prob {A: Type} (pset: list A) (prob: A -> R): R :=
  sum (map prob pset).

Module ProbDistr.

Record Distr (A: Type): Type := {
  prob: A -> R;
  pset: list A;
}.

Arguments prob {_} _.
Arguments pset {_} _.

Record legal {A: Type} (d: Distr A): Prop := {
  legal_no_dup: NoDup d.(pset);
  legal_nonneg: forall a, (d.(prob) a >= 0)%R;
  legal_pset_valid: forall a, (d.(prob) a > 0)%R -> In a d.(pset);
  legal_prob_1: sum_prob d.(pset) d.(prob) = 1%R;
}.

Definition equiv {A: Type} (d1 d2: Distr A): Prop :=
  (forall a: A, d1.(prob) a = d2.(prob) a) /\
  Permutation d1.(pset) d2.(pset).

(*
  Description:
    whether exists an implication relation from d1 to d2.
    i.e.,
    Can d1 be partitioned into disjoint ∪ E_i, 
    and d2 be partitioned into disjoint ∪ F_i,

    so that for all i:
      E_i -> F_i.
      /\
      Prob[E_i] = Prob[F_i]

    (here 'imply' means forall p ∈ E_i, q ∈ F_i, p->q).

  Argument:
     d1 d2 : Distr Prop.

  Note:
    L is a list pair(list Prop, list Prop)
      concat (map fst L) -> a partition of d1's outcomes (Prop).
      concat (map snd L) -> a partition of d2's outcomes (Prop).
    
  for (event1, event2) ∈ L 
    forall Prop P1 ∈ event1, Prop P2 ∈ event2.
      P1 -> P2.
    /\
    Prob[event1] = Prob[event2]
*)
Definition imply_event (d1 d2: Distr Prop): Prop :=
  exists L: list (list Prop * list Prop),
    Permutation d1.(pset) (concat (map fst L)) /\
    Permutation d2.(pset) (concat (map snd L)) /\
    (forall l1 l2,
       In (l1, l2) L ->
       forall P1, In P1 l1 ->
       forall P2, In P2 l2 ->
       In P2 l2 -> (* duplicated line? *)
       (P1 -> P2)) /\
    (forall l1 l2,
       In (l1, l2) L ->
       sum_prob l1 d1.(prob) = sum_prob l2 d2.(prob)).

Definition equiv_event (d1 d2: Distr Prop): Prop :=
  exists L: list (list Prop * list Prop),
    Permutation d1.(pset) (concat (map fst L)) /\
    Permutation d2.(pset) (concat (map snd L)) /\
    (forall l1 l2,
       In (l1, l2) L ->
       forall P1, In P1 l1 ->
       forall P2, In P2 l2 ->
       In P2 l2 ->
       (P1 <-> P2)) /\
    (forall l1 l2,
       In (l1, l2) L ->
       sum_prob l1 d1.(prob) = sum_prob l2 d2.(prob)).

Definition is_det {A: Type} (a: A) (d: Distr A): Prop :=
  d.(pset) = [a] /\ d.(prob) a = 1%R /\
  forall b, (a <> b) -> d.(prob) b = 0%R.

(** This definition should only be used when ds contains
    positive probabilities. *)
Record sum_distr {A: Type}
                 (ds: list (R * Distr A))
                 (d0: Distr A): Prop :=
{
  sum_pset_valid:
    forall a, In a d0.(pset) <->
              In a (concat (map (fun '(r, d) => d.(pset)) ds));
  sum_prob_valid:
    forall a, d0.(prob) a =
              sum (map (fun '(r, d) => r * d.(prob) a) ds)%R;
}.

(* check if r = Prob[true Prop in d.(pset)] *)
Definition compute_pr (d: Distr Prop) (r: R): Prop :=
  exists (l: list Prop),
    (forall P, In P l <-> In P d.(pset) /\ P) /\
    sum_prob l d.(prob) = r.
  
End ProbDistr.

Notation "'Distr'" := (ProbDistr.Distr) (at level 0).
Notation "x '.(pset)'" := (ProbDistr.pset x) (at level 1).
Notation "x '.(prob)'" := (ProbDistr.prob x) (at level 1).
Notation "x '.(legal_no_dup)'" := (ProbDistr.legal_no_dup _ x) (at level 1).
Notation "x '.(legal_nonneg)'" := (ProbDistr.legal_nonneg _ x) (at level 1).
Notation "x '.(legal_pset_valid)'" := (ProbDistr.legal_pset_valid _ x) (at level 1).
Notation "x '.(legal_prob_1)'" := (ProbDistr.legal_prob_1 _ x) (at level 1).



(*
  Name: 
    filter_true_prop_list_exists

  Property:
    Auxiliary Theorm
  
  Description:
    For a list of Prop: L,
    A list of Prop: l exists, s.t. 
      l = filter (P is true) L.
      i.e., l contains exactly all true Props in L.

  Note: 
    direct filter is not feasible, so a existential statement is necessary.
*)
Theorem filter_true_prop_list_exists:
  forall L : list Prop, exists l : list Prop, (forall P, In P l <-> In P L /\ P).
Proof.
  induction L as [| Ph tl].
  - exists [].
    intros.
    simpl.
    tauto.
  - destruct IHtl as [l0 H0].
    destruct (classic Ph). (*cases analysis on Ph is true or false*)
    + exists (Ph::l0).
      intros.
      split; intros; specialize (H0 P) as H0.
      *  (* In P Ph::l0 -> *)
        destruct H1.
        ++ subst P. (* P = Ph*)
          split; [left; tauto | tauto].
        ++ (* P != Ph, thus P in l0 *)  
          apply H0 in H1.
          split; [right; tauto | tauto].
      * (* In P (Ph :: tl) /\ P -> *)    
        destruct H1.
        destruct H1.
        ++ subst P.
          left.
          reflexivity.
        ++ right.
          apply H0.
          tauto.
    + exists l0. (* Ph::tl, Ph is false*)
      intros.
      split; intros; specialize (H0 P) as H0.
      * (* In P l0 -> In P (Ph :: tl) /\ P *)
        apply H0 in H1.
        split; [right; tauto | tauto].
      * (* In P (Ph :: tl) /\ P -> In P l0 *)
        assert (In P tl) as H_tl.
        {
          destruct H1.
          destruct H1.
          + subst P. contradiction.
          + exact H1.
        }
        apply H0.
        tauto.
Qed.

(* 
  Description:
    for any distribution on Props: d,
      Prob[true Props in d] exists (witness r).
*)

Theorem ProbDistr_compute_pr_exists: forall d, exists r,
  ProbDistr.compute_pr d r.
(* Admitted. * Level 1 *)
Proof.
  intros.
  unfold ProbDistr.compute_pr.
  specialize (filter_true_prop_list_exists d.(pset)) as H_true_list.
  destruct H_true_list as [l_true_list H_true_list].
  exists (sum_prob l_true_list d.(prob)).
  exists l_true_list.
  intros.
  tauto.
Qed.

(*
  Description:
    Reflexivity of imply_event.
*)
#[export] Instance ProbDistr_imply_event_refl:
  Reflexive ProbDistr.imply_event.
(* Admitted. * Level 1 *)
Proof.
  unfold Reflexive.
  intros.
  unfold ProbDistr.imply_event.
  exists (map (fun p => ([p], [p])) x.(pset)).
  assert (forall (A : Type) (l : list A),
  Permutation l (concat (map (fun x => [x]) l))) as H_perm_concat_map_singleton.
  {
    intros A l.
    induction l as [| h tl HIHl]; simpl.
    - reflexivity.
    - rewrite <- HIHl.
      reflexivity.
  }
  repeat split; simpl; 
  [
    rewrite map_map; simpl; apply H_perm_concat_map_singleton
    |rewrite map_map; simpl; apply H_perm_concat_map_singleton 
    | 
    |
  ].
  + 
    (* goal P1 = P2*)
    intros.
    apply in_map_iff in H.
    destruct H as [P0 [H' H'']].
    inversion H'.
    subst l1 l2.
    simpl in *.
    assert (P0 = P1) as H_eq1. {
      destruct H0; [exact H | tauto ].
    }
    assert (P0 = P2) as H_eq2. {
      destruct H1; [exact H | tauto ].
    }
    subst P1 P2.
    exact H3.
  + intros.
    apply in_map_iff in H.
    destruct H as [P0 [H' H'']].
    inversion H'.
    reflexivity.
Qed.
    

(*
  Description:
    Reflexivity of imply_event under equivalence.
*)
Theorem ProbDistr_imply_event_refl_setoid:
  forall d1 d2, ProbDistr.equiv_event d1 d2 -> ProbDistr.imply_event d1 d2.
(* Admitted. * Level 1 *)
  intros.
  unfold ProbDistr.equiv_event in H.
  destruct H as [L H].
  unfold ProbDistr.imply_event.
  exists L.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  destruct H3 as [H3 H4].

  repeat split; simpl; [
    apply H1 |
    apply H2 |
    |
  ].
  clear H1 H2.
  + intros.
    specialize (H3 l1 l2 H P1 H0 P2 H1 H1).
    (* 
    specialize (H3 l1 l2).
    specialize (H3 H).
    specialize (H3 P1).
    specialize (H3 H0).
    specialize (H3 P2).
    repeat specialize (H3 H1). *)
    rewrite <-H3.
    exact H5.
  + intros.
    specialize (H4 l1 l2 H).
    exact H4.
Qed.
    
(* 
  Description:
    ProbDistr.equiv is indeed an Equivalence relation.
*)
#[export] Instance ProbDistr_equiv_equiv {A: Type}:
  Equivalence (@ProbDistr.equiv A).
(* Admitted. * Level 1 *)
Proof.
  unfold ProbDistr.equiv.
  split.
  - (* Reflexivity*)
    unfold Reflexive.
    intro x.
    split; [reflexivity | reflexivity].
  - (* Symmetric *)
    unfold Symmetric.
    intros x y H.
    destruct H as [H1 H2].
    split.
    + symmetry. 
      specialize (H1 a).
      exact H1.
    + symmetry.
      exact H2.
  - (* Transitivity *)
    unfold Transitive.
    intros.
    destruct H as [H1a H1b].
    destruct H0 as [H2a H2b].
    split.
    + intros.
      specialize (H1a a).
      specialize (H2a a).
      rewrite H1a, H2a.
      reflexivity.
    + rewrite H1b, H2b.
      reflexivity.
Qed.

#[export] Instance ProbDistr_imply_event_trans:
  Transitive ProbDistr.imply_event.
Admitted. (** Level 1 *)

#[export] Instance ProbDistr_equiv_event_equiv:
  Equivalence ProbDistr.equiv_event.
Admitted. (** Level 1 *)

#[export] Instance ProbDistr_imply_event_congr:
  Proper (ProbDistr.equiv_event ==>
          ProbDistr.equiv_event ==> iff) ProbDistr.imply_event.
Admitted. (** Level 1 *)

#[export] Instance ProbDistr_compute_pr_congr:
  Proper (ProbDistr.equiv_event ==> Sets.equiv) ProbDistr.compute_pr.
Admitted. (** Level 1 *)

Theorem ProbDistr_compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbDistr.compute_pr f1 r1 ->
    ProbDistr.compute_pr f2 r2 ->
    ProbDistr.imply_event f1 f2 ->
    (r1 <= r2)%R.
Admitted. (** Level 1 *)

(*********************************************************)
(**                                                      *)
(** Probability Monad                                    *)
(**                                                      *)
(*********************************************************)

Module ProbMonad.

Record Legal {A: Type} (f: Distr A -> Prop): Prop := {
  Legal_exists: exists d, d ∈ f;
  Legal_legal: forall d, d ∈ f -> ProbDistr.legal d;
  Legal_unique: forall d1 d2, d1 ∈ f -> d2 ∈ f -> ProbDistr.equiv d1 d2;
}.

Record M (A: Type): Type :=
{
  distr: Distr A -> Prop;
  legal: Legal distr;
}.

Arguments distr {_} _.
Arguments legal {_} _.

Definition __ret {A: Type} (a: A) : Distr A -> Prop :=
  ProbDistr.is_det a.

Lemma __ret_Legal {A: Type}: forall a: A, Legal (__ret a).
Admitted.

Definition ret {A: Type} (a: A) : M A :=
  {|
    distr := __ret a;
    legal := __ret_Legal a;
  |}.

Definition __bind {A B: Type}
                  (f: Distr A -> Prop)
                  (g: A -> Distr B -> Prop)
                  (s2: Distr B): Prop :=
  exists (s1: Distr A) l,
    s1 ∈ f /\
    Forall2
      (fun a '(r, d) =>
         r = s1.(prob) a /\ d ∈ g a)
      s1.(pset) l /\
    ProbDistr.sum_distr l s2.

Lemma __bind_legal {A B: Type}:
  forall (f: Distr A -> Prop) (g: A -> Distr B -> Prop),
    Legal f ->
    (forall a, Legal (g a)) ->
    Legal (__bind f g).
Admitted.

Definition bind {A B: Type} (f: M A) (g: A -> M B): M B :=
  {|
    distr := __bind f.(distr) (fun a => (g a).(distr));
    legal := __bind_legal _ _ f.(legal) (fun a => (g a).(legal));
  |}.

Definition compute_pr (f: M Prop): SetMonad.M R :=
  fun r => exists (d: Distr Prop), d ∈ f.(distr) /\ ProbDistr.compute_pr d r.

Definition imply_event (f1 f2: M Prop): Prop :=
  exists d1 d2,
    d1 ∈ f1.(distr) /\ d2 ∈ f2.(distr) /\ ProbDistr.imply_event d1 d2.

Definition equiv {A: Type} (f1 f2: M A): Prop :=
  f1.(distr) == f2.(distr).

Definition equiv_event (f1 f2: M Prop): Prop :=
  exists d1 d2,
    d1 ∈ f1.(distr) /\ d2 ∈ f2.(distr) /\ ProbDistr.equiv_event d1 d2.

End ProbMonad.

#[export] Instance ProbMonad: Monad ProbMonad.M := {|
  bind := @ProbMonad.bind;
  ret := @ProbMonad.ret;
|}.

Notation "x == y" := (ProbMonad.equiv x y): monad_scope.
Notation "x === y" := (ProbMonad.equiv_event x y) (at level 61): monad_scope.
Notation "x '.(distr)'" := (ProbMonad.distr x) (at level 1).
Notation "x '.(legal)'" := (ProbMonad.legal x) (at level 1).
Notation "x '.(Legal_exists)'" := (ProbMonad.Legal_exists _ x) (at level 1).
Notation "x '.(Legal_legal)'" := (ProbMonad.Legal_legal _ x) (at level 1).
Notation "x '.(Legal_unique)'" := (ProbMonad.Legal_unique _ x) (at level 1).

Definition Always {A: Type} (c: ProbMonad.M A) (P: A -> Prop): Prop :=
  Hoare (ProbMonad.compute_pr (res <- c;; ret (P res))) (fun pr => pr = 1%R).

Theorem Always_conseq: forall {A: Type} (P Q: A -> Prop),
  (forall a, P a -> Q a) ->
  (forall c, Always c P -> Always c Q).
Admitted. (** Level 1 *)

Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
Proof.
Admitted. (** Level 1 *)

Theorem compute_pr_exists: forall f, exists r, ProbMonad.compute_pr f r.
Proof.
  intros.
  unfold ProbMonad.compute_pr.
  pose proof f.(legal).(Legal_exists) as [d ?].
  pose proof ProbDistr_compute_pr_exists d as [r ?].
  exists r, d.
  tauto.
Qed.

#[export] Instance ProbMonad_imply_event_refl:
  Reflexive ProbMonad.imply_event.
Admitted. (** Level 2 *)

Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_equiv_equiv {A: Type}:
  Equivalence (@ProbMonad.equiv A).
Proof.
  unfold ProbMonad.equiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_equiv_event_equiv:
  Equivalence ProbMonad.equiv_event.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_imply_event_congr:
  Proper (ProbMonad.equiv_event ==>
          ProbMonad.equiv_event ==> iff) ProbMonad.imply_event.
Admitted. (** Level 2 *)

#[export] Instance compute_pr_congr:
  Proper (ProbMonad.equiv_event ==> Sets.equiv) ProbMonad.compute_pr.
Admitted. (** Level 2 *)

Theorem compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbMonad.compute_pr f1 r1 ->
    ProbMonad.compute_pr f2 r2 ->
    ProbMonad.imply_event f1 f2 ->
    (r1 <= r2)%R.
Admitted.

#[export] Instance ProbMonad_bind_congr (A B: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv ==>
          ProbMonad.equiv)
    (@bind _ ProbMonad A B).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_bind_mono_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.imply_event ==>
          ProbMonad.imply_event)
    (@bind _ ProbMonad A Prop).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_ret_mono_event:
  Proper (Basics.impl ==> ProbMonad.imply_event) ret.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_ret_congr_event:
  Proper (iff ==> ProbMonad.equiv_event) ret.
Admitted. (** Level 2 *)

Lemma bind_assoc:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Admitted. (** Level 3 *)

Lemma bind_assoc_event:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M Prop),
  ProbMonad.equiv_event
    (bind (bind f g) h)
    (bind f (fun a => bind (g a) h)).
Admitted. (** Level 3 *)

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> ProbMonad.M B),
  bind (ret a) f == f a.
Admitted. (** Level 3 *)

Lemma bind_ret_l_event:
  forall (A: Type)
         (a: A)
         (f: A -> ProbMonad.M Prop),
  ProbMonad.equiv_event (bind (ret a) f) (f a).
Admitted. (** Level 3 *)

Lemma bind_ret_r:
  forall (A: Type)
         (f: ProbMonad.M A),
  bind f ret == f.
Admitted. (** Level 3 *)

