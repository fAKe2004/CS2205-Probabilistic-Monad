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

(***
  eq_dec adds-on
***)

(**
  Name: 
    eq_dec

  Property:
    Axiom
  
  Description:
    decidable equality for any type A.

  Note: 
    when need to check two elements are equal or not, you can use this function to destruct the result.
    eg : destruct (eq_dec a b) as [H_equal | H_neq].
*)
Axiom eq_dec: forall {A: Type} (x y: A), {x = y} + {x <> y}.

(*
  Name: 
    eq_dec_refl

  Property:
    Auxilary Theorem
  
  Description:
    eq_dec is a reflexive realtion and the result of eq_dec a a = left eq_refl.
*)
Lemma eq_dec_refl: forall {A: Type} (a: A), eq_dec a a = left eq_refl.
Proof.
  intros A a.
  destruct (eq_dec a a).
  - f_equal.
    apply proof_irrelevance.
  - contradiction.
Qed.

(*
  Name: 
    not_equal_symmetry

  Property:
    Auxilary Theorem
  
  Description:
    not_equl for Type A is symmetric , if x <> y, then y <> x.
*)
Lemma not_equal_symmetry : forall (A : Type) (x y : A), x <> y -> y <> x.
Proof.
  intros A x y H.
  unfold not in *.
  intros H1.
  apply H.
  rewrite H1.
  reflexivity.
Qed.

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

(* check if r = Prob[true Prop in d.(pset)] *)
Definition compute_pr (d: Distr Prop) (r: R): Prop :=
  exists (l: list Prop),
    NoDup l /\
    (forall P, In P l <-> In P d.(pset) /\ P) /\
    sum_prob l d.(prob) = r.


(* updated new imply_event *)

Definition imply_event (d1 d2: Distr Prop): Prop :=
  exists r1 r2,
    compute_pr d1 r1 /\
    compute_pr d2 r2 /\
    (r1 <= r2)%R.
  
Definition equiv_event (d1 d2: Distr Prop): Prop :=
  exists r1 r2,
    compute_pr d1 r1 /\
    compute_pr d2 r2 /\
    r1 = r2.
  
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
  Property: Auxiliary Theorem
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
  Name: 
    no_dup_in_equiv_list_exists
  Property: Auxiliary Theorem
  Description:
    for any list l, 
      a list l' contains same set of elements as l and has no duplication exists.
*)
Theorem no_dup_in_equiv_list_exists:
  forall {A: Type} (l: list A),
      exists l':list A,
        NoDup l' /\ (forall a: A, In a l <-> In a l').
Proof.
  intros.
  induction l as [| a lt IHl].
  + exists [].
    split.
    - constructor.
    - intros.
      reflexivity.
  + destruct IHl as [lt' [H1 H2]].
    destruct (classic (In a lt)).
    - (* case 1 a in lt, then lt' itself*)
      exists lt'.
      split; [exact H1| ].
      intros.
      split.
      * intros.
        destruct H0; 
        [subst a; specialize(H2 a0); tauto 
        | specialize(H2 a0); tauto].

      * intros.
        specialize (H2 a0).
        apply H2 in H0.
        right.
        tauto.
    - (* case 2 a not in lt, then a::lt'*)
      exists (a::lt').
      split.
      * constructor; [specialize(H2 a); tauto | exact H1].
      * intros.
        specialize(H2 a0).
        split.
        -- intros [H0 | H0].
           ++ subst. left. reflexivity.
           ++ right. apply H2. exact H0.
        -- intros [H0 | H0].
           ++ subst. left. reflexivity.
           ++ right. apply H2. exact H0.
Qed.
    
(* 
  Description:
    for any distribution on Props: d,
      Prob[true Props in d] exists (witness r).
*)

Theorem ProbDistr_compute_pr_exists: forall d, exists r,
  ProbDistr.compute_pr d r.
Proof.
  intros.
  unfold ProbDistr.compute_pr.
  destruct (filter_true_prop_list_exists d.(pset)) as [l H].
  specialize (no_dup_in_equiv_list_exists l) as [l' H'].
  destruct H' as [H1 H2].
  assert (forall P: Prop, In P l' <-> In P d.(pset) /\ P) as H3. {
    intros.
    specialize (H P).
    specialize (H2 P).
    rewrite <-H.
    tauto.
  }

  exists (sum_prob l' d.(prob)).
  exists l'; split; [apply H1 |]; split; [ | reflexivity].
  intro P.
  specialize (H3 P).
  exact H3.
Qed.


Lemma Permutation_in:
  forall {A: Type} (l1 l2: list A) (x: A),
    Permutation l1 l2 -> In x l1 -> In x l2.
Admitted.
  
Theorem Permutation_sum_eq:
  forall (l1 l2: list R),
    Permutation l1 l2 ->
    sum l1 = sum l2.
Proof.
  intros l1 l2 Hperm.
  induction Hperm.
  - reflexivity.
  - simpl. rewrite IHHperm. reflexivity.
  - simpl. 
    repeat rewrite <- Rplus_assoc.
    rewrite (Rplus_comm y x).
    reflexivity.
  - rewrite IHHperm1. assumption.
Qed.

Lemma Permutation_sum_map_eq:
  forall (l1 l2: list Prop) (f1 f2: Prop -> R),
    Permutation l1 l2 ->
    (forall x, f1 x = f2 x) ->
    sum (map f1 l1) = sum (map f2 l2).
Admitted.
  

(*
  Name: ProbDistr_equiv_equiv_event
  Property: Auxiliary Theorem
  Description:
    for any two distributions d1 d2,
      if d1 equiv d2, then d1 equiv_event d2.
*)
Theorem ProbDistr_equiv_equiv_event:
  forall (d1 d2: Distr Prop),
    ProbDistr.equiv d1 d2 -> ProbDistr.equiv_event d1 d2.
Proof.
  intros.
  destruct H as [H8 H9].
  unfold ProbDistr.equiv_event.
  destruct (filter_true_prop_list_exists d1.(pset)) as [l1 H1].
  specialize (no_dup_in_equiv_list_exists l1) as [l2 H2].
  destruct (filter_true_prop_list_exists d2.(pset)) as [l3 H3].
  specialize (no_dup_in_equiv_list_exists l3) as [l4 H4].
  destruct H2 as [H2a H2b].
  destruct H4 as [H4a H4b].
  assert (forall P: Prop, In P l2 <-> In P d1.(pset) /\ P) as H2c. {
    intros.
    specialize (H2b P).
    specialize (H1 P).
    rewrite <-H1.
    tauto.
  }
  assert (forall P: Prop, In P l4 <-> In P d2.(pset) /\ P) as H4c. {
    intros.
    specialize (H4b P).
    specialize (H3 P).
    rewrite <-H3.
    tauto.
  }
  exists (sum_prob l2 d1.(prob)), (sum_prob l4 d2.(prob)).
  split; [ | split].
  - exists l2; split; [exact H2a | split; [exact H2c | reflexivity]].
  - exists l4; split; [exact H4a | split; [exact H4c | reflexivity]].
  - assert (Permutation l2 l4) as Hperm. {
      apply NoDup_Permutation; [exact H2a | exact H4a |].
      intros x.
      specialize (H2c x).
      specialize (H4c x).
      split; intros.
      + apply H2c in H.

        apply H4c.
        split.
        2:{apply H. }
        -- apply Permutation_in with (l1:=d1.(pset)).
          --- exact H9.
          --- apply H.
      + apply H4c in H.

      apply H2c.
      split.
      2:{apply H. }
      -- apply Permutation_in with (l1:=d2.(pset)).
        --- rewrite H9. reflexivity.
        --- apply H.
    }
    unfold sum_prob.
    apply Permutation_sum_map_eq.
    exact Hperm.
    apply H8.
Qed.




(*
  Name: 
    no_dup_in_equiv_Permutation:
  Property: Auxiliary Theorem
  Description:
    for any two list l1 l2.
      if l1 l2 has no duplication and l1 l2 contain same set of elements.
      then Permutation l1 l2.
  
  额，幽默一刻之标准库里好像有。用 NoDup_Permutation 即可。
*)
(* Theorem no_dup_in_equiv_Permutation:
  forall {A: Type} (l1 l2: list A),
    NoDup l1 -> NoDup l2 ->
    (forall a: A, In a l1 <-> In a l2) ->
    Permutation l1 l2.
Proof.
  intros.
  apply NoDup_Permutation; [exact H | exact H0 |].
  intros.
  split; intros.
  - specialize (H1 x).
    tauto.
  - specialize (H1 x).
    tauto.
Qed. *)



(*
  Description:
    for any distribution on Props: d
      exactly one r satisfies compute_pr d r
*)  
Theorem ProbDistr_compute_pr_unique: 
  forall d r1 r2,
  ProbDistr.compute_pr d r1 -> 
  ProbDistr.compute_pr d r2 -> 
  r1 = r2.
Proof.
  intros.
  destruct H as [l1 [H1a [H1b H1c]]].
  destruct H0 as [l2 [H2a [H2b H2c]]].
  subst.
  unfold sum_prob.
  assert (Permutation l1 l2) as H_perm. {
    apply NoDup_Permutation; [assumption| assumption|].
    intros x.
    rewrite H1b.
    rewrite H2b.
    reflexivity.
  }
  assert (Permutation (map d.(prob) l1) (map d.(prob) l2)) as H_perm'. {
    apply Permutation_map.
    exact H_perm.
  }
  apply (Permutation_sum_eq (map d.(prob) l1) (map d.(prob) l2) H_perm').
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
  unfold ProbDistr.imply_event.
  intro d.
  specialize (ProbDistr_compute_pr_exists d) as [r H].
  exists r, r.
  split; [exact H | split; [exact H | lra]].
Qed.
  
(*
  Description:
    Reflexivity of imply_event under equivalence.
*)
Theorem ProbDistr_imply_event_refl_setoid:
  forall d1 d2, ProbDistr.equiv_event d1 d2 -> ProbDistr.imply_event d1 d2.
Proof.
  intros.
  destruct H as [r1 [r2 [H1 [H2 H3]]]].
  unfold ProbDistr.imply_event.
  exists r1, r2.
  split; [exact H1 | split; [exact H2 | lra]].
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



(*
  Description:
    Transitivity of imply_event. *)
#[export] Instance ProbDistr_imply_event_trans:
  Transitive ProbDistr.imply_event.
(* Admitted. * Level 1 *)
Proof.
  unfold Transitive.
  intros x y z H1 H2.
  unfold ProbDistr.imply_event in *.
  destruct H1 as [r1 [r2 [H1 [H3 H4]]]].
  destruct H2 as [r2' [r3 [H2 [H5 H6]]]].
  exists r1, r3.
  specialize (ProbDistr_compute_pr_unique y r2 r2' H3 H2) as H7.
  split.
  - exact H1.
  - split.
    + exact H5.
    + lra.
Qed.


(*
  Description:
    Equivalence of events is an equivalence relation.
*)
#[export] Instance ProbDistr_equiv_event_equiv:
  Equivalence ProbDistr.equiv_event.
Proof.
  unfold ProbDistr.equiv_event.
  split.
  - (* Reflexivity *)
    unfold Reflexive.
    intros x.
    destruct (ProbDistr_compute_pr_exists x) as [r H].
    exists r, r.
    split; [exact H | split; [exact H | lra]].
  - (* Symmetric *)
    unfold Symmetric.
    intros x y H.
    destruct H as [r1 [r2 [H1 [H2 H3]]]].
    exists r2, r1.
    split; [exact H2 | split; [exact H1 | lra]].
  - (* Transitivity *)
    unfold Transitive.
    intros x y z H1 H2.
    destruct H1 as [r1 [r2 [H1 [H3 H4]]]].
    destruct H2 as [r2' [r3 [H2 [H5 H6]]]].
    exists r1, r3.
    specialize (ProbDistr_compute_pr_unique y r2 r2' H3 H2) as H7.
    split.
    + exact H1.
    + split.
      * exact H5.
      * lra.
Qed.  

(* 
  Description:
    This instance proves that the `ProbDistr.imply_event` relation 
      is preserved under the `ProbDistr.equiv_event` equivalence.
    Specifically, if two distributions `x` and `y` are equivalent 
      and two other distributions `z` and `w` are also equivalent,
      then the implication relationship between `x` and `z` is 
      logically equivalent to the implication relationship between `y` and `w`.
*)
#[export] Instance ProbDistr_imply_event_congr:
  Proper (ProbDistr.equiv_event ==>
          ProbDistr.equiv_event ==> iff) ProbDistr.imply_event.
Proof.
  unfold Proper, respectful.
  intros x y H1 z w H2.
  split; intros H.
  - unfold ProbDistr.imply_event in *.
    destruct H as [r1 [r2 [H3 [H4 H5]]]].
    destruct H1 as [r1' [r2' [H6 [H7 H8]]]].
    destruct H2 as [r1'' [r2'' [H9 [H10 H11]]]].
    exists r1', r2''.
    split.
    + subst r1'.
      exact H7.
    + split.
      * exact H10.
      * (specialize (ProbDistr_compute_pr_unique x r1 r1' H3 H6) as H12).
        subst r1'.
        (specialize (ProbDistr_compute_pr_unique z r2 r1'' H4 H9) as H13).
        lra.
  - unfold ProbDistr.imply_event in *.
    destruct H as [r1 [r2 [H3 [H4 H5]]]].
    destruct H1 as [r1' [r2' [H6 [H7 H8]]]].
    destruct H2 as [r1'' [r2'' [H9 [H10 H11]]]].
    exists r1', r1''.
    split.
    + exact H6.
    + split.
      * exact H9.
      * specialize (ProbDistr_compute_pr_unique y r1 r2' H3 H7) as H12.
        specialize (ProbDistr_compute_pr_unique w r2 r2'' H4 H10) as H13.
        lra.
Qed.


(**
  Description:
    ProbDistr.compute_pr is a congruence relation under ProbDistr.equiv

  i.e. : 
    ProbDistr.equiv_event d1 d2 -> 
      ProbDistr.compute_pr d1 = ProbDistr.compute_pr d2
*)
#[export] Instance ProbDistr_compute_pr_congr:
  Proper (ProbDistr.equiv_event ==> Sets.equiv) ProbDistr.compute_pr.
Proof.
  unfold Proper, respectful.
  intros d1 d2 H.
  destruct H as [r1 [r2 [H1 [H2 H3]]]].
  split.
  - intros.
    specialize (ProbDistr_compute_pr_unique d1 r1 a H1 H) as H4.
    rewrite <- H4.
    rewrite <- H3 in H2.
    tauto.
  - intros.
    specialize (ProbDistr_compute_pr_unique d2 r2 a H2 H) as H4.
    rewrite <- H4.
    rewrite H3 in H1.
    tauto.
Qed.
(** Admitted.  Level 1 *)

(**
  Description:
    the imply_event relation can imply the montonicity of compute_pr relation.
*)
Theorem ProbDistr_compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbDistr.compute_pr f1 r1 ->
    ProbDistr.compute_pr f2 r2 ->
    ProbDistr.imply_event f1 f2 ->
    (r1 <= r2)%R.
Proof.
  intros.
  destruct H1 as [r1' [r2' [H1 [H2 H3]]]].
  specialize (ProbDistr_compute_pr_unique f1 r1 r1' H H1) as H4.
  specialize (ProbDistr_compute_pr_unique f2 r2 r2' H0 H2) as H5.
  subst.
  tauto.
Qed.
(**Admitted.  Level 1 *)


(*********************************************************)
(**                                                      *)
(** Probability Monad                                    *)
(**                                                      *)
(*********************************************************)

Module ProbMonad.

Record Legal {A: Type} (f: Distr A -> Prop): Prop := {
  (* exists a unique legal Distr d in f *)
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


(**
  Description:
    Legal of __ret a.
*)
Lemma __ret_Legal {A: Type}: forall a: A, Legal (__ret a).
Proof.
  intros.
  unfold __ret, ProbDistr.is_det.
  split.
  - exists {| 
      ProbDistr.prob := fun x => if eq_dec x a then 1%R else 0%R;
      ProbDistr.pset := [a]
    |}.
    split; simpl.
    + reflexivity.
    + split.
      * rewrite eq_dec_refl.
        lra.
      * intros.
        destruct (eq_dec b a).
        -- exfalso. 
           apply H.
           rewrite e.
           reflexivity.
        -- tauto.
  - intros.
    destruct H as [Hpset [Hprob1 Hprob2]].
    split.
    + rewrite Hpset.
      apply NoDup_cons.
      * simpl;tauto.
      * simpl.
        apply NoDup_nil.
    + intros.
      destruct (eq_dec a0 a).
      * subst.
        rewrite Hprob1.
        lra.
      * specialize (Hprob2 a0).
        apply not_equal_symmetry in n.
        specialize (Hprob2 n).
        rewrite Hprob2.
        lra.
    + intros.
      destruct (eq_dec a0 a).
      * rewrite e, Hpset.
        apply in_eq.
      * specialize (Hprob2 a0).
        apply not_equal_symmetry in n.
        specialize (Hprob2 n).
        lra.
    + rewrite Hpset.
      unfold sum_prob.
      simpl.
      rewrite Hprob1.
      lra.
  - intros.
    destruct H as [H_d1_pset [H_d1_prob1 H_d1_prob2]].
    destruct H0 as [H_d2_pset [H_d2_prob1 H_d2_prob2]].
    unfold ProbDistr.equiv.
    split.
    + intros.
      destruct (eq_dec a0 a).
      * subst.
        rewrite H_d1_prob1, H_d2_prob1.
        reflexivity.
      * apply not_equal_symmetry in n.
        specialize (H_d1_prob2 a0 n).
        specialize (H_d2_prob2 a0 n).
        rewrite H_d1_prob2, H_d2_prob2.
        reflexivity.
    + rewrite H_d1_pset, H_d2_pset.
      apply Permutation_refl.
Qed.
         
      

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

(*
  Name: compute_pr_unique
  Property: Auxiliary Theorem
  Description:
    ProbMonad verson of ProbDistr_comput_pr_unique.
*)

Theorem compute_pr_unique: 
  forall f r1 r2,
  ProbMonad.compute_pr f r1 -> 
  ProbMonad.compute_pr f r2 -> 
  r1 = r2.
Proof.
  intros.
  unfold ProbMonad.compute_pr in *.
  destruct H as [d1 [H1a H1b]].
  destruct H0 as [d2 [H2a H2b]].
  pose proof (f.(legal).(Legal_unique) d1 d2 H1a H2a) as H_unique.
  specialize (ProbDistr_equiv_equiv_event d1 d2 H_unique).
  unfold ProbDistr.equiv_event.
  intros.
  destruct H as [r1' H].
  destruct H as [r2' H].
  destruct H as [H1b' [H2b' H_eq]].
  specialize (ProbDistr_compute_pr_unique d1 r1 r1' H1b H1b') as H_unique1.
  specialize (ProbDistr_compute_pr_unique d2 r2 r2' H2b H2b') as H_unique2.
  subst r1.
  subst r2.
  tauto.
Qed.

#[export] Instance ProbMonad_imply_event_refl:
  Reflexive ProbMonad.imply_event.
Proof.
  unfold Reflexive.
  intros x.
  unfold ProbMonad.imply_event.
  destruct (ProbMonad.Legal_exists _ x.(legal)) as [d1 ?].
  exists d1, d1.
  split.
  + exact H.
  + split.
    - exact H.
    - apply ProbDistr_imply_event_refl.
Qed.
(**Admitted. Level 2 *)

Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Proof.
  intros.
  unfold ProbMonad.equiv_event in H.
  destruct H as [r1 [r2 [H1 [H2 H3]]]].
  unfold ProbMonad.imply_event.
  exists r1, r2.
  split.
  - exact H1.
  - split.
    + exact H2.
    + apply ProbDistr_imply_event_refl_setoid.
      exact H3.
Qed.
(**Admitted.  Level 2 *)

#[export] Instance ProbMonad_equiv_equiv {A: Type}:
  Equivalence (@ProbMonad.equiv A).
Proof.
  unfold ProbMonad.equiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Proof.
  intros x y z H1 H2.
  unfold ProbMonad.imply_event in *.
  destruct H1 as [d1 [d2 [H3 [H4 H5]]]].
  destruct H2 as [d2' [d3 [H6 [H7 H8]]]].
  exists d1, d3.
  split.
  - exact H3. 
  - split.
    + exact H7.
    + pose proof y.(legal).(Legal_unique) as H9.
      specialize (H9 d2 d2' H4 H6).
      apply ProbDistr_imply_event_trans with d2.
      * exact H5.
      * apply ProbDistr_imply_event_trans with d2'.
      2:{ exact H8. }
      apply ProbDistr_imply_event_refl_setoid.
      apply ProbDistr_equiv_equiv_event in H9.
      exact H9.
Qed.

(**Admitted. Level 2 *)

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

(* TODO *)
#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Proof.
  unfold Proper, respectful.
  intros fx fy H_eq_f gx gy H_eq_g.
  unfold ProbMonad.equiv_event in *.
  unfold pointwise_relation in H_eq_g.
  eexists.
  eexists.
  repeat split.
Admitted.
(* Admitted. * Level 2 *)

Theorem is_det_compute_pr_01:
  



#[export] Instance ProbMonad_ret_mono_event:
  Proper (Basics.impl ==> ProbMonad.imply_event) ret.
Proof.
  unfold Proper, respectful.
  unfold Basics.impl.
  intros.
  unfold ProbMonad.imply_event.
  pose proof (ret x).(legal).(Legal_exists) as [d1 ?].
  pose proof (ret y).(legal).(Legal_exists) as [d2 ?].
  exists d1.
  exists d2.
  split; [tauto | ].
  split; [tauto | ].
  unfold ret in *.
  simpl in *.
  unfold ProbMonad.__ret, ProbDistr.is_det in *.
  destruct H0 as [H1a [H1b H1c]].
  destruct H1 as [H2a [H2b H2c]].
  unfold ProbDistr.imply_event.

  asser
  destruct (classic x) as [Hx | Hnx].
  - exists 1%R, 1%R.
    split.
    assert (
      forall d: Distr Prop,
        forall a: Prop,
    )
(* Admitted. * Level 2 *)

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

