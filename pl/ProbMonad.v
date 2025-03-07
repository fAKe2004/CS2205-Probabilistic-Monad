Require Import Coq.Reals.Reals. 
Require Import Coq.Reals.RList.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope list.

(* Adds on *)
Require Import Classical.

(*********************************************************)
(**                                                      *)
(** General Auxiliary Theorems                           *)
(**                                                      *)
(*********************************************************)

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

(*
  Name forall_exists_Forall2_exists:
  Property: Auxiliary Theorem
  Description:
    if forall a, exists b s.t. P a b is satisfied, then 
    forall l1: list A, 
      exists l2: list B s.t. Forall2 P l1 l2 is satisfied
*)
Theorem forall_exists_Forall2_exists:
  forall {A B: Type} (rel: A->B->Prop) (l1: list A),
    (forall a : A, exists b : B, rel a b) -> exists l2, Forall2 rel l1 l2.
Proof.
  intros.
  induction l1 as [| head ltail].
  - exists [].
    constructor.
  - destruct IHltail as [ltail' IH].
    specialize (H head).
    destruct H as [head' Hhead'].
    exists (head' :: ltail').
    constructor; [tauto | tauto].
Qed.

Lemma Permutation_Forall2_equiv_list_trans:
  forall {B : Type}  (equiv: B->B->Prop) (l1 ltrans_1 l12 ltrans_2 l2 : list B),
  (Equivalence equiv)
  -> Permutation l1 ltrans_1
  -> Forall2 equiv ltrans_1 l12
  -> Permutation l12 ltrans_2
  -> Forall2 equiv ltrans_2 l2
  -> exists l1' : list B, Permutation l1 l1' /\ Forall2 equiv l1' l2.
Admitted.


Theorem Permutation_Forall2_equiv_list_exists:
  forall {A B : Type} (rel: A->B->Prop) (equiv: B->B->Prop) (lp1 lp2 : list A) (l1 l2 : list B),
    (
      forall (a : A) (b1 b2 : B),
        rel a b1 -> rel a b2 -> equiv b1 b2
    )
    -> (
      forall (a : A), exists b : B,
        rel a b
    )
    -> (Equivalence equiv)
    -> Permutation lp1 lp2
    -> Forall2 rel lp1 l1
    -> Forall2 rel lp2 l2
    -> exists l1', Permutation l1 l1' /\ Forall2 equiv l1' l2.
Proof.
  intros ? ? ? ? ? ? ? ? Hrel_equiv Hrel_ex Hequiv_equiv Hlp Hl1 Hl2.
  revert dependent l2.
  revert dependent l1.
  induction Hlp as [| xp lp1t lp2t | xp yp lpt | lp lp' lp'']; intros.
  (* | perm_nil : Permutation [] [] *)
  + exists nil.
    inversion Hl1; subst; clear Hl1.
    inversion Hl2; subst; clear Hl2.
    split; [constructor | constructor].
  (*  
        | perm_skip : forall (x : A) (l l' : list A), Permutation l l' -> Permutation (x :: l) (x :: l') 
        *)
  + inversion Hl1 as [| ? head1 ? l1t Hhead1 Htail1]; subst; clear Hl1.
    inversion Hl2 as [| ? head2 ? l2t Hhead2 Htail2]; subst; clear Hl2.
    specialize (IHHlp l1t Htail1 l2t Htail2) as [l1' [Hperm Hl1']].
    exists (head1 :: l1').
    split.
    - constructor. exact Hperm.
    - constructor.
      * specialize (Hrel_equiv xp head1 head2 Hhead1 Hhead2).
        exact Hrel_equiv.
      * exact Hl1'.
  (*
    | perm_swap : forall (x y : A) (l : list A), Permutation (y :: x :: l) (x :: y :: l)
  *)
  + inversion Hl1 as [| ? y1 ? l1t Hy1 Hl1t]; subst; clear Hl1.
    inversion Hl1t as [| ? x1 ? l1tt Hx1 Hl1tt]; subst; clear Hl1t.
    
    inversion Hl2 as [| ? x2 ? l2t Hx2 Hl2t]; subst; clear Hl2.
    inversion Hl2t as [| ? y2 ? l2tt Hy2 Hl2tt]; subst; clear Hl2t.

    exists (x1 :: y1 :: l1tt).
    split.
    - constructor.
    - assert (
        equiv x1 x2
      ) as Hx_eq by ( specialize (Hrel_equiv xp x1 x2 Hx1 Hx2);exact Hrel_equiv).

      assert (
        equiv y1 y2
      ) as Hy_eq by ( specialize (Hrel_equiv yp y1 y2 Hy1 Hy2);exact Hrel_equiv).

      constructor; [tauto |].
      constructor; [tauto |].

      revert dependent l2tt.
      revert dependent l1tt.
      induction lpt as [| head lptt IHlp]; intros.
      * inversion Hl1tt; subst; clear Hl1tt.
        inversion Hl2tt; subst; clear Hl2tt.
        constructor.
      * inversion Hl1tt as [| ? z1 ? l1ttt Hhead1 Hl1ttt]; subst; clear Hl1tt.
        inversion Hl2tt as [| ? z2 ? l2ttt Hhead2 Hl2ttt]; subst; clear Hl2tt.
        specialize (IHlp l1ttt Hl1ttt l2ttt Hl2ttt) as Hlttt.
        assert (
          equiv z1 z2
        ) as Hz_eq by ( specialize (Hrel_equiv head z1 z2 Hhead1 Hhead2);exact Hrel_equiv).
        constructor; tauto.
  + 
    assert (
      exists l12, Forall2 rel lp' l12) as [l12 Hl12] . {
      apply forall_exists_Forall2_exists.
      exact Hrel_ex.
    }

    specialize (IHHlp1 l1 Hl1 l12 Hl12) as [ltrans_1].
    specialize (IHHlp2 l12 Hl12 l2 Hl2) as [ltrans_2].

    (* l1 -> ltrans_1 -> l12 -> ltrans_2 -> l2*)
    apply (Permutation_Forall2_equiv_list_trans equiv l1 ltrans_1 l12 ltrans_2 l2); tauto.
Qed.
(* 遗憾的是这里 trans 不过去了，因为显示构造没有了。理论上是 l1 和 ltrans_2 对照一下下标，变换一下得到目标 l1', 但是由于过了一层 l12, Permutation l1 ltrans_2 没有了。*)




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

(* Definition compute_pr_eval(d: Distr Prop): R :=
  sum_prob (filter (fun P: Prop =>  if eq_dec P True then true else false) d.(pset)) d.(prob). *)

(*
  r = compute_pr_eval d
  then compute_pr d r
*)
(* Lemma compute_pr_eval_correctness:
  forall d: Distr Prop,
    legal d ->
    compute_pr d (compute_pr_eval d).
*)
  

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
  sum_pset_no_dup: (* adds on to enforce d0.(pset)'s validity*)
    NoDup d0.(pset);
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

    
(* 
  Description:
    compute_pr is non negative if d is legal
*)

Theorem ProbDistr_compute_pr_nonneg: forall (d : Distr Prop) (r: R),
  ProbDistr.legal d -> (ProbDistr.compute_pr d r) ->
  (r >= 0)%R.
Proof.
  intros.
  destruct H0 as [l [H1 [H2 H3]]].
  clear H1 H2.
  revert H3.
  revert r.
  unfold sum_prob.
  induction l as [| a tl IHl]; simpl in *; intros.
  - lra.
  - specialize (IHl (sum (map d.(prob) tl))).
    assert (H_ge0_tl: (sum (map d.(prob) tl) >= 0)%R). {
      apply IHl.
      reflexivity.
    }
    subst r.
    specialize (ProbDistr.legal_nonneg d H a) as H_ge0_a.
    lra.
Qed.

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

(* updated: accept general type *)
Lemma Permutation_sum_map_eq:
  forall {A: Type} (l1 l2: list A) (f1 f2: A -> R),
    Permutation l1 l2 ->
    (forall x, f1 x = f2 x) ->
    sum (map f1 l1) = sum (map f2 l2).
    Proof.
    intros.
    apply Permutation_sum_eq.
    specialize (Permutation_map f1 H).
    intros.
    apply Permutation_trans with (map f1 l2).
    + exact H1.
    +
      clear H1.
      clear H.
      induction l2.
      * simpl. reflexivity.
      * simpl.
        rewrite IHl2.
        specialize (H0 a).
        rewrite H0.
        reflexivity.
  Qed.

(**
  Name: ProbDistr_equiv_equiv_event
  Property: Auxiliary Theorem
  Description:
    for any two distributions d1 d2,
      if d1 d2 are equivalent, then d1 d2 are equivalent in event.
    i.e., 
      for any two distributions d1 d2,
        ProbDistr.equiv d1 d2 -> ProbDistr.equiv_event d1 d2.
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
          -- apply Permutation_in with (l:=d1.(pset)).
            --- exact H9.
            --- apply H.
        + apply H4c in H.
        apply H2c.
        split.
        2:{apply H. }
        -- apply Permutation_in with (l:=d2.(pset)).
          --- rewrite H9. reflexivity.
          --- apply H.
      }
      unfold sum_prob.
      apply Permutation_sum_map_eq.
      exact Hperm.
      apply H8.
  Qed.


(*
  Name: ProbDistr_equiv_legal_congr
  Property: Auxiliary Theorem
  Description:
    if d1 ~=~ d2 -> legal d1 -> legal d2
*)
Theorem ProbDistr_equiv_legal_congr:
  forall {A: Type} (d1 d2: Distr A),
    ProbDistr.equiv d1 d2 -> ProbDistr.legal d1 -> ProbDistr.legal d2.
Proof.
  intros ? ? ? Hequiv Hlegal1.
  destruct Hequiv as [Hprob Hpset].
  destruct Hlegal1 as [HNoDup Hnonneg Hpset_valid Hprob_1].
  split.
  - apply (Permutation_NoDup Hpset HNoDup).
  - intro a.
    rewrite <-(Hprob a).
    apply (Hnonneg a).
  - intros a Hprob_g0.
    specialize (Hpset_valid a).
    rewrite <-(Hprob a) in Hprob_g0.
    apply Hpset_valid in Hprob_g0 as H_in.
    specialize (Permutation_in) as Hfinal.
    apply (Hfinal A d1.(pset) d2.(pset) a); assumption.
  - unfold sum_prob in *.
    rewrite <-(Permutation_sum_map_eq d1.(pset) d2.(pset) d1.(prob) d2.(prob)); assumption.
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


(*
  Name: ProbDistr_biliteral_imply_event_iif_equiv_event:
  Property: Auxiliary Theorem.
  Description:
    biliteral imply event <-> equiv_event.
*)
Theorem ProbDistr_biliteral_imply_event_iif_equiv_event:
  forall d1 d2,
    (ProbDistr.imply_event d1 d2 /\ ProbDistr.imply_event d2 d1) <-> ProbDistr.equiv_event d1 d2.
Proof.
  intros.
  split.
  - intros [H1 H2].
    unfold ProbDistr.equiv_event.
    destruct H1 as [r1 [r2 [Hcp1 [Hcp2 Hrel]]]].
    destruct H2 as [r2' [r1' [Hcp2' [Hcp1' Hrel']]]].
    pose proof (ProbDistr_compute_pr_unique d1 r1 r1' Hcp1 Hcp1') as Heq_r1.
    subst r1'.
    pose proof (ProbDistr_compute_pr_unique d2 r2 r2' Hcp2 Hcp2') as Heq_r2.
    subst r2'.
    exists r1, r2.
    split; [exact Hcp1 | split; [exact Hcp2 | lra]].
  - intros H.
    unfold ProbDistr.imply_event.
    destruct H as [r1 [r2 [Hcp1 [Hcp2 Heq]]]].
    split. 
    + exists r1, r2.
      repeat split; [exact Hcp1 | exact Hcp2 | lra].
    + exists r2, r1.
      repeat split; [exact Hcp2 | exact Hcp1 | lra].
Qed.


(*
  Name is_det_exists
  Property: Auxiliary Theorem
  Description:
    for any element a: A, there exists a deterministic distribution d s.t. is_det a d.
*)

Theorem is_det_exists:
  forall {A: Type} (a: A),
    exists d: Distr A, ProbDistr.is_det a d.
Proof.
  intros A a.
  exists {| 
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
Qed.


(* 
  Name: ProbDistr_sum_distr_exists
  Property: Auxiliary Theorem
  Description:
    For any list of weighted distributions, there exists a summed distribution.

  used to prove the __bind_legal: Legal_exists.
*)
Theorem ProbDistr_sum_distr_exists:
  forall {A: Type} (l: list (R * Distr A)),
    exists d, ProbDistr.sum_distr l d.
Proof.
  intros.
  pose proof (no_dup_in_equiv_list_exists (concat (map (fun '(r, d) => d.(pset)) l))) as [l' H]. 
  exists {|
    ProbDistr.prob := fun a => sum (map (fun '(r, d) => r * d.(prob) a)%R l);
    ProbDistr.pset := l'
  |}.
  split.
  - simpl.
    destruct H as [? _].
    apply H.
  - intros.
    destruct H as [_ H].
    split.
    + intros.
      simpl in H0.
      rewrite H.
      apply H0.
    + intros.
      simpl.
      rewrite <- H.
      apply H0.
  - intros.
    simpl.
    reflexivity.
Qed.

(*
  Name: ProbDistr_not_in_pset_prob_0:
  Property: Auxiliary Theorem
  Description:
    if d is legal, then ~In a d.(pset) -> d.(prob) a = 0.

  ... just to save time of reasoning this every time whenever you need it.
*)
Theorem ProbDistr_not_in_pset_prob_0:
  forall {A: Type} (d : Distr A) (a : A),
    ProbDistr.legal d->
   ~In a d.(pset) ->  d.(prob) a = 0%R.
Proof.
  intros.
  destruct H.
  apply Rle_antisym.
  - destruct (classic (d.(prob) a > 0)%R).
    + specialize (legal_pset_valid a H).
      contradiction.
    + nra.
  - specialize (legal_nonneg a).
    nra.
Qed.

Theorem ProbDistr_sum_distr_legal_aux1_aux:
  forall {A: Type} (l1 : list (A->R)) (l2 : list A),
    sum (map (fun x => sum (map (fun f => f x) l1)) l2)
    = 
    sum (map (fun f => sum (map f l2)) l1).
Proof.
  intros.
  symmetry.
  induction l2 as [| a l2tail IHl2]; simpl.
  - induction l1 as [| f l1tail IH]; simpl.
    + reflexivity.
    + rewrite IH.
      nra.
  - rewrite <-IHl2; clear IHl2.
    induction l1 as [| f l1tail IHl1]; simpl.
    + nra.
    + rewrite IHl1.
      nra.
Qed.
(* just an attmpt to seek the essence of ProbDistr_sum_distr_legal_aux1, succeeded! (though this aux1_aux is not actually used) *)

(* direct auxiliary theorem for ProbDistr_sum_distr
  maybe resuable in other proof.

  essence : swap of summation order.
*)
Theorem ProbDistr_sum_distr_legal_aux1:
  forall {A: Type} (l1: list (R * Distr A)) (l2 : list A),
    (sum 
      (map 
        (fun a => (sum (map (fun '(r, d) => (r * d.(prob) a)) 
          l1)))
      l2) 
    =
     sum 
      (map 
        (fun '(r, d) => r * sum (map d.(prob) l2)) 
          l1)
    )%R.
Proof.
  intros.
  symmetry.

  induction l2 as [| a l2tail IHl2]; simpl.
  - induction l1 as [| [r d] l1tail IHl2]; simpl.
    + reflexivity.
    + rewrite IHl2.
      nra.
  - rewrite <-IHl2; clear IHl2.
    induction l1 as [| [r d] l1tail IHl1]; simpl.
    + nra.
    + rewrite IHl1.
      nra.
Qed. 

(* direct auxiliary theorem for ProbDistr_sum_distr_legal_aux2 *)
Theorem ProbDistr_sum_distr_legal_aux2_aux:
  forall {A: Type} (l1 l2 : list A) (f: A->R),
    NoDup l1 ->
    NoDup l2 ->
    (forall a, In a l1 -> In a l2) ->
    (forall a, ~In a l1 -> f a = 0%R) ->
    sum (map f l1) = sum (map f l2).
Proof.
  intros A l1 l2 f H_nodup1 H_nodup2 H_subset H_zero.
  
  (* Define a boolean membership test function *)
  assert (exists in_test : A -> bool,
          forall x, In x l1 <-> in_test x = true) as [in_test H_in_test].
  {
    exists (fun x => if In_dec eq_dec x l1 then true else false).
    intros x.
    destruct (In_dec eq_dec x l1); split; intro H; try discriminate; auto.
  }
  
  (* First, prove by induction on any list l:
     sum (map f l) = sum (map f (filter in_test l)) *)
  assert (forall l, sum (map f l) = sum (map f (filter in_test l))) as H_filter_eq.
  {
    induction l as [|x l' IH].
    - (* Base case: empty list *)
      simpl. reflexivity.
    - (* Inductive case *)
      simpl.
      destruct (in_test x) eqn:H_test.
      + (* x is in l1 *)
        simpl. f_equal.
        exact IH.
      + (* x is not in l1 *)
        specialize (H_in_test x) as H_in_test_x.
        assert (~ In x l1) as H_not_in_l1.
        {
          unfold not.
          intros H_in.
          apply H_in_test_x in H_in.
          rewrite H_test in H_in.
          discriminate.
        }
        specialize (H_zero x H_not_in_l1).
        rewrite H_zero.
        rewrite Rplus_0_l.
        exact IH.
  }
  specialize (H_filter_eq l2) as H_filter_eq_l2.
  rewrite H_filter_eq_l2.
  
  (* Next, prove that filter in_test l2 is a permutation of l1 *)
  assert (Permutation l1 (filter in_test l2)) as H_perm.
  {
    apply NoDup_Permutation.
    - exact H_nodup1.
    - apply NoDup_filter.
      exact H_nodup2.
    - intro a.
      split; intro H_in.
      + (* -> direction *)
        apply filter_In.
        split.
        * apply H_subset. exact H_in.
        * apply H_in_test. exact H_in.
      + (* <- direction *)
        apply filter_In in H_in.
        destruct H_in as [_ H_in].
        apply H_in_test in H_in.
        exact H_in.
  }
  
  (* Finally, use permutation to show sums are equal *)
  apply Permutation_map with (f:=f) in H_perm.
  apply Permutation_sum_eq.
  exact H_perm.
Qed.

(* direct auxiliary theorem for ProbDistr_sum_distr_legal *)
Theorem ProbDistr_sum_distr_legal_aux2:
  forall {A: Type} (l: list (R * Distr A)) (lpset : list A),
    Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l ->
    NoDup lpset ->
    (forall a : A,
      In a
        (concat
          (map (fun '(_, d) => d.(pset)) l))
      -> In a lpset) (* key difference, this makes induction possible compared to <->*)
    -> 
    (sum
      (map
        (fun '(r, d) => (r * sum (map d.(prob) lpset)))
          l) 
    =
    sum
      (map
        (fun '(r, d) => (r * sum (map d.(prob) d.(pset)))) 
          l) )%R.
Proof.
  intros ? ? ? HForall HNoDup_lpset Hin_imply.
  induction l as [| head ltail IH]; simpl.
  - reflexivity.
  - destruct head as [r d].
    inversion HForall as [| ? ? Hhead Htail]; subst.
    specialize (IH Htail).

    assert (forall a : A,
    In a
      (concat
         (map (fun '(_, d) => d.(pset)) ltail)) ->
    In a lpset) as Hin_imply_tail. {
      intros.
      apply Hin_imply.
      simpl.
      apply in_app_iff.
      right.
      exact H.
    }
    specialize (IH Hin_imply_tail).
    rewrite IH; clear IH Hin_imply_tail Htail HForall.
    (* remains:
        r * sum (map d.(prob) lpset) = r * sum (map d.(prob) d.(pset)
    *)
    assert (
      forall a,
        In a d.(pset) -> In a lpset
    ) as Hin_imply_head. {
      intros.
      apply Hin_imply.
      simpl.
      apply in_app_iff.
      left.
      exact H.
    }
    clear Hin_imply.
    destruct Hhead as [_ Hhead].
    assert (sum (map d.(prob) lpset) = sum (map d.(prob) d.(pset)))
    as H_eq. {
      symmetry.
      apply ProbDistr_sum_distr_legal_aux2_aux with (l1 := d.(pset)) (l2 := lpset).
      - destruct Hhead.
        apply legal_no_dup.
      - apply HNoDup_lpset.
      - exact Hin_imply_head.
      - intros.
        apply ProbDistr_not_in_pset_prob_0.
        + apply Hhead.
        + exact H.
    }
    rewrite H_eq.
    reflexivity.
Qed.

(* 
  Name: ProbDistr_sum_distr_legal
  Property: Auxiliary Theorem
  Description:
    if the Forall (r, d) in l : r >= 0 /\ legal d, 
    then ds: sum_distr l ds, ds is legal.

  used to prove __bind_legal: Legal_legal (i.e., resulting distribution is legal )
*)
Theorem ProbDistr_sum_distr_legal:
  forall {A: Type} (l: list (R * Distr A)) (ds: Distr A),
    Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l ->
    sum (map (fun '(r, d) => r) l) = 1%R ->
    ProbDistr.sum_distr l ds ->
    ProbDistr.legal ds.
Proof.
  intros A l ds HForall Hsum_r Hsum_distr.
  split.
  - (* NoDup *)
    destruct Hsum_distr as [? _ _].
    exact sum_pset_no_dup.
  - (* Legal_nonneg *)
    intros.
    destruct Hsum_distr as [_ _ Hprob].
    rewrite Hprob. (* have to rewrite first to avoid redundant assumption at induction *)
    clear Hprob Hsum_r.
    induction l as [| head l_tail].
    + simpl.
      nra.
    + 
    assert (Forall
    (fun '(r, d) =>
     (r >= 0)%R /\
     ProbDistr.legal d) l_tail) as Hl_tail. {
      inversion HForall; tauto.
     }
     specialize (IHl_tail Hl_tail) as Hl_tail_ge0.
     destruct head as [r d].
     simpl.

     assert ((r * d.(prob) a >= 0)%R) as Hhead_ge0. {
      inversion HForall.
      destruct H1 as [Hr_ge0 Hd_legal].
      pose proof (ProbDistr.legal_nonneg d Hd_legal) as Hproba_ge0.
      specialize (Hproba_ge0 a).
      nra.
    }
    nra.
  - (* Legal_pset_valid *)
    intros a H_g0.
    destruct (classic (In a ds.(pset))) as [H_in | H_not_in].
    + exact H_in.
    + exfalso. (* lead to contradiction with H_g0 *)
      destruct Hsum_distr as [_ Hpset Hprob].

      assert ((ds.(prob) a = 0)%R) as H_eq0. {
        clear H_g0.
        rewrite Hprob.
        rewrite Hpset in H_not_in.
        clear Hsum_r Hprob Hpset.
        induction l as [| head ltail IH]; simpl.
        - reflexivity.
        - destruct head as [r d]; simpl in *.
          assert (
            Forall
            (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d)
            ltail
          ) as Hltail by (inversion HForall; tauto).
          assert (
            (r >= 0)%R /\ ProbDistr.legal d
          ) as Hhead by (inversion HForall; tauto).
          
          specialize (IH Hltail).

          assert (~In a
            (concat
               (map (fun '(_, d) => d.(pset))
                  ltail))
          ) as H_not_in_tail. {
            clear IH Hltail Hhead HForall.
            unfold not in *.
            intro H_in.
            apply H_not_in.
            apply in_app_iff.
            right.
            exact H_in.
          }

          specialize (IH H_not_in_tail).
          rewrite IH. (*rewrite sum tail prob = 0*)
          
          destruct Hhead as [_ Hlegal].
          destruct Hlegal as [_ Hnon_neg Hpset _].
          specialize (Hnon_neg a).
          specialize (Hpset a).
          assert ((d.(prob) a <= 0)%R) as Hle0. {
            apply Rnot_gt_le.
            intro Hpos.
            specialize (Hpset Hpos) as H_in.
            apply H_not_in.
            clear HForall IH Hltail Hnon_neg Hpset H_not_in_tail H_not_in.
            apply in_app_iff; left.
            exact H_in.
          }
          assert ((d.(prob) a = 0)%R) as H_eq0 by (nra).
          nra.
      }
      (* H_eq0 H_g0 contradiction*)
      nra.
  - (* Legal_prob_1 *)
    unfold sum_prob.
    (* goal: 
        sum (map ds.(prob) ds.(pset)) = 1

        method:
          FIRST:
            forall lpset : list A
                1. for a in lpset:
                    sum += ds.(prob) a

                2. for (r, d) in l:
                    for a in lpset:
                      tmp += d.(prob) a
                    sum += tmp
             these 2 summations are equal. (prove by induction)

          SECOND:
            sum [map (fun '(r, d) => r * sum (map d.(prob) d.(pset))]) l] = 1 (trivial)

          To prove FIRST, H_aux0 to H_aux2 are used.
    *)
    destruct Hsum_distr as [Hnodup Hpset Hprob].

    assert ( 
      (* rewrite with sum_distr prob definition *)
      forall lpset : list A,
        (sum 
          (map 
            (fun a => 
              (sum (map (fun '(r, d) => (r * d.(prob) a)) l)))
          lpset) = sum (map ds.(prob) lpset))%R
    ) as H_aux0. {
      clear HForall Hnodup Hpset.
      intro.
      induction lpset as [| head lpset' IH]; simpl.
      - reflexivity.
      - rewrite IH; clear IH.
        specialize (Hprob head).
        rewrite Hprob.
        reflexivity.
    }

    assert ( 
      (* prove that, 
          for i in [N], for j in [M]: sum += f_i (a_j)
          <=>
          for j in [M], for i in [N]: sum += f_i (a_j)

         [in perfect N*M rectangle shape, 
          we use lpset to pad d.(pset) to align it to ds.(pset)].
      *)
      forall lpset : list A,
        (sum 
          (map 
            (fun a => 
              (sum (map (fun '(r, d) => (r * d.(prob) a)) l)))
          lpset) =
        sum (map (fun '(r, d) => r * sum (map d.(prob) lpset)) l))%R
    ) as H_aux1. {
      intro lpset.
      specialize (ProbDistr_sum_distr_legal_aux1 l lpset) as H_aux.
      exact H_aux.
    }

    assert (
      (*
        convert the perfect rectangle shape to irregular shape.
        remove padding[whose prob = 0] which aligns d.(pset) to ds.(pset).
      *)
      (sum
        (map
          (fun '(r, d) => (r * sum (map d.(prob) ds.(pset)))) 
            l) 
       =
       sum
        (map
          (fun '(r, d) => (r * sum (map d.(prob) d.(pset)))) 
            l) 
      )%R
    ) as H_aux2. {
      clear H_aux0 H_aux1.
      assert (forall a : A, In a (concat (map (fun '(_, d) => d.(pset)) l)) -> In a ds.(pset)) as Hin_imply. {
        intro a.
        specialize (Hpset a).
        tauto.
      }
      
      specialize (ProbDistr_sum_distr_legal_aux2 l ds.(pset) HForall Hnodup Hin_imply) as H.
      exact H.
    } (* H_aux2 *)

    assert (
      (* apply (legal d-> legal_prob_1 d) elementwise into l *)
      (* the resulting form is the same as Hsum_r, so we are done *)
      (sum
        (map
          (fun '(r, d) => (r * sum (map d.(prob) d.(pset)))) 
            l) 
        = 
       sum (map
          (fun '(r, d) => r) 
            l) 
      )%R
    ) as H_aux3. {
      clear Hsum_r Hnodup Hpset Hprob.
      clear H_aux0 H_aux1 H_aux2.
      induction l as [| head ltail IH]; simpl.
      - reflexivity.
      - destruct head as [r d].
        assert (
          Forall
            (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) ltail) 
        as Hl_tail 
        by (inversion HForall; tauto).
        specialize (IH Hl_tail).
        rewrite IH.

        assert (
          (r * sum (map d.(prob) d.(pset)) = r)%R
        )
        as H_head. {
          inversion HForall; subst.
          destruct H1 as [_ [_ _ _ Hlegal_prob]].
          unfold sum_prob in Hlegal_prob.
          rewrite Hlegal_prob.
          nra.
        }

        rewrite H_head.
        reflexivity.
    } (* H_aux3 *)


    specialize (H_aux0 ds.(pset)).
    specialize (H_aux1 ds.(pset)).
    rewrite <-H_aux0.
    rewrite H_aux1.
    rewrite H_aux2.
    rewrite H_aux3.
    apply Hsum_r.
Qed.




(* (*
  Name: ProbDistr_sum_distr_unique
  Property: Auxiliary Theorem
  Description:
    if l, ds1, ds2:
      sum_distr l ds1 /\ sum_distr l ds2
      -> equiv ds1 ds2
*)
Theorem ProbDistr_sum_distr_unique:
  forall {A: Type} (l: list (R * Distr A)) (ds1 ds2: Distr A),
    ProbDistr.sum_distr l ds1 ->
    ProbDistr.sum_distr l ds2 ->
    ProbDistr.equiv ds1 ds2.
Admitted. *)

(*
  Name: ProbDistr_sum_distr_same_list_congr
  Property: Auxiliary Theorem
  Description:
    if l, ds1, ds2:
      equiv ds1 ds2 /\ sum_distr l ds1
      -> sum_distr l ds2
*)
Theorem ProbDistr_sum_distr_same_list_congr:
  forall {A: Type} (l: list (R * Distr A)) (ds1 ds2: Distr A),
    ProbDistr.equiv ds1 ds2 ->
    ProbDistr.sum_distr l ds1 ->
    ProbDistr.sum_distr l ds2.
Proof.
  intros ? ? ? ? Hequiv Hds1.
  destruct Hds1 as [Hnodup Hpset Hprob].
  destruct Hequiv as [Hprob_equiv Hpset_equiv].
  split.
  - apply Permutation_NoDup with (l := ds1.(pset)); assumption.
  - intro a.
    rewrite <-Hpset_equiv.
    apply Hpset.
  - intro a.
    rewrite <-Hprob_equiv.
    apply Hprob.
Qed.




(*
  Name: ProbDistr_sum_distr_permutation_equiv
  Property: Auxiliary Theorem
  Description:
    Permutation L1 L1' -> sum_distr over L1 L1' is equivalent (assume legality)
*)
Theorem ProbDistr_sum_distr_permutation_equiv:
  forall {B: Type} (L1 L1' : list (R * Distr B)) (ds1 ds1' : Distr B),
  Permutation L1 L1'
  -> ProbDistr.sum_distr L1 ds1
  -> ProbDistr.sum_distr L1' ds1'
  -> (forall a : B,
  (ds1.(prob) a > 0)%R ->
  In a ds1.(pset)) (* pset valid *)
  -> (forall a : B,
  (ds1'.(prob) a > 0)%R ->
  In a ds1'.(pset)) (* pset valid *)
  -> ProbDistr.equiv ds1 ds1'.
Proof.
  intros ? ? ? ? ? Hperm H1 H2 H_pset_valid1 H_pset_valid2.
  rename L1' into L2.
  rename ds1' into ds2.
  destruct H1 as [H_no_dup1 Hpset1 Hprob1].
  destruct H2 as [H_no_dup2 Hpset2 Hprob2].
  unfold ProbDistr.equiv.
  assert (Permutation ds1.(pset) ds2.(pset)) as H_perm_ds1_ds2. {
    apply NoDup_Permutation; [tauto | tauto |].
    intro a.
    specialize (Hpset1 a).
    specialize (Hpset2 a).
    rewrite Hpset1.
    rewrite Hpset2.
    assert (Permutation (concat (map (fun '(_, d) => d.(pset)) L1)) (concat (map (fun '(_, d) => d.(pset)) L2))) as Hperm'.
    {
      clear Hpset1 Hpset2 Hprob1 Hprob2.
      clear H_no_dup1 H_no_dup2 H_pset_valid1 H_pset_valid2.
      clear a ds1 ds2.
      induction Hperm.
      - simpl. constructor.
      - simpl. apply Permutation_app.
        + reflexivity.
        + exact IHHperm.
      - simpl.
        destruct x as [_ x'].
        destruct y as [_ y'].
        rewrite (app_assoc x'.(pset) y'.(pset)).
        rewrite (Permutation_app_comm x'.(pset) y'.(pset)).
        rewrite (app_assoc y'.(pset) x'.(pset)).
        reflexivity.
      - rewrite IHHperm1.
        exact IHHperm2.
    }
    split; apply Permutation_in.
    - tauto.
    - symmetry; tauto.
  }
  split.
  2 : {
    exact H_perm_ds1_ds2.
  }
  intro a.
  specialize (Hprob1 a).
  specialize (Hprob2 a).
  rewrite Hprob1.
  rewrite Hprob2.
  apply Permutation_map with (f:=(fun '(r, d) => (r * d.(prob) a)%R)) in Hperm.
  apply Permutation_sum_eq; assumption.
Qed.

(*
  Name: ProbDistr_sum_distr_equiv_equiv
  Property: Auxiliary Theorem
  Description:
    Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) L1 L2
    -> sum_distr L1 ~=~ sum_distr L2
*)
Theorem ProbDistr_sum_distr_equiv_equiv:
  forall {B: Type} (L1 L2 : list (R * Distr B)) (ds1 ds2 : Distr B),
  Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) L1 L2
  -> ProbDistr.sum_distr L1 ds1
  -> ProbDistr.sum_distr L2 ds2
  -> ProbDistr.equiv ds1 ds2.
Proof.
  intros B L1 L2 ds1 ds2 HForall2 Hsum1 Hsum2.
  destruct Hsum1 as [Hnodup1 Hpset1 Hprob1].
  destruct Hsum2 as [Hnodup2 Hpset2 Hprob2].
  split.
  - intro a.
    specialize (Hprob1 a).
    specialize (Hprob2 a).
    rewrite Hprob1.
    rewrite Hprob2.
    clear dependent ds1.
    clear dependent ds2.
    induction HForall2 as [| x y L1t L2t Hhead Htail IH]; simpl.
    + reflexivity.
    + rewrite IH.
    destruct x as [rx dx].
    destruct y as [ry dy].
    destruct Hhead as [Hr Hd].
    destruct Hd as [Hprob_eq _].
    rewrite (Hprob_eq a).
    rewrite Hr.
    reflexivity.
  - apply (NoDup_Permutation Hnodup1 Hnodup2).
    intro a.
    clear Hnodup1 Hnodup2 Hprob1 Hprob2.
    rewrite (Hpset1 a); clear Hpset1.
    rewrite (Hpset2 a); clear Hpset2.
    assert (Permutation (concat (map (fun '(_, d) => d.(pset)) L1)) (concat (map (fun '(_, d) => d.(pset)) L2))) as Hperm. {
      clear a ds1 ds2.
      induction HForall2 as [| [rx dx] [ry dy] L1t L2t [Hr Hd] Htail IH]; simpl.
      - constructor.
      - apply Permutation_app.
        + destruct Hd; tauto.
        + exact IH.
    }
    split; intro Hin.
    + apply Permutation_in with (l := concat (map (fun '(_, d) => d.(pset)) L1)); assumption.
    + symmetry in Hperm.
      apply Permutation_in with (l := concat (map (fun '(_, d) => d.(pset)) L2)); assumption.
Qed.







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
  (* congruence under ProbDistr.equiv*)
  Legal_congr: forall d1 d2, ProbDistr.equiv d1 d2 -> d1 ∈ f -> d2 ∈ f;
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
  - specialize (is_det_exists a) as [d Hd].
    exists d.
    exact Hd.
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
  - intros d1 d2 H_equiv.
    intro Hd1.
    destruct Hd1 as [Hpset [Hprob1 Hprob0]].
    unfold ProbDistr.equiv in H_equiv.
    destruct H_equiv as [Hprob_equiv Hpset_equiv].
    repeat split.
    + rewrite Hpset in Hpset_equiv.
      apply Permutation_length_1_inv in Hpset_equiv.
      exact Hpset_equiv.
    + specialize (Hprob_equiv a).
      rewrite Hprob1 in Hprob_equiv.
      symmetry in Hprob_equiv.
      exact Hprob_equiv.
    + intros b Hb.
      specialize (Hprob0 b Hb).
      specialize (Hprob_equiv b).
      rewrite Hprob0 in Hprob_equiv.
      symmetry in Hprob_equiv.
      exact Hprob_equiv.
Qed.         
(* Admitted. level 2? *)

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


(*
  Property: Auxiliary Theorem
*)
Lemma get_distr_from_legal {A : Type} {g : A -> Distr A -> Prop} (a : A) (Hg : Legal (g a)) : exists d : Distr A, d ∈ g a.
Proof.
  destruct Hg as [ex _ _].
  exact ex.
Qed.




(*
  Name: ProbDistr_sum_distr_legal_precondition_helper
  Property: Auxiliary Theorem
  Description:
    To convert common condition in bind f g, into precondition for sum_distr_legal
*)
Theorem ProbDistr_sum_distr_legal_precondition_helper:
  forall {A B: Type} (f: Distr A -> Prop) (g: A -> Distr B -> Prop)  (df : Distr A) (l : list (R * Distr B)),
  Legal f ->
  (forall a : A, Legal (g a)) ->
  df ∈ f ->
  Forall2 (fun (a : A) '(r, d) => r = df.(prob) a /\ d ∈ g a) df.(pset) l ->
  Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l /\
  sum (map (fun '(r, d) => r) l) = 1%R.
Proof.
  intros ? ? ? ? ? ? Hf Hg Hdf Hl.
  split.
  * induction Hl as [| x y lx_tail ly_tail].
    - constructor.
    - destruct y as [r d].
      destruct H as [Hr Hd].
      constructor.
      + destruct Hf as [_ Hdf_legal _ _].
        specialize (Hdf_legal df Hdf).
        pose proof (ProbDistr.legal_nonneg df Hdf_legal) as H_ge0.
        specialize (H_ge0 x).
        subst r.
        
        specialize (Hg x) as Hg.
        destruct Hg as [_ Hd_legal _ _].
        specialize (Hd_legal d Hd).
        tauto.
      + exact IHHl.
  * assert ( (* summation r = 1, prerequisite for ProbDistr_sum_distr_legal *)
      sum (map (fun '(r, d) => r) l) = 1%R
    ) as Hsum_r. {
      assert (sum (map (fun '(r, d) => r) l) = sum (map (df.(prob)) df.(pset))) as H_aux.
      {
        induction Hl as [| x [r d] lx_tail ly_tail [Hr Hd] Htail]; simpl.
        - reflexivity.
        - rewrite IHHtail.
          rewrite <-Hr.
          reflexivity.    
      }
      rewrite H_aux.
      destruct Hf as [_ Hdf_legal _ _].
      specialize (Hdf_legal df Hdf).
      destruct Hdf_legal as [_ _ _ Hsum_prob1].
      unfold sum_prob in Hsum_prob1.
      exact Hsum_prob1.
    }
    apply Hsum_r.
Qed.



Lemma __bind_legal {A B: Type}:
    forall (f: Distr A -> Prop) (g: A -> Distr B -> Prop),
      Legal f ->
      (forall a, Legal (g a)) ->
      Legal (__bind f g).
Proof.
  intros f g Hf Hg.

  assert (
    forall d : Distr B, d ∈ __bind f g -> ProbDistr.legal d
    ) as HLegal_legal. {
  intros ds Hds.
  destruct Hds as [df [l [Hdf [Hl Hsum_distr]]]].

  specialize (ProbDistr_sum_distr_legal_precondition_helper f g df l Hf Hg Hdf Hl) as [Hl_Forall_legal Hsum_r].

  specialize (ProbDistr_sum_distr_legal l ds Hl_Forall_legal Hsum_r Hsum_distr) as Hds_legal. (* key auxiliary theorem *)
  exact Hds_legal.
  } (* to be reused in Legal_unique *)

  split.
  - (* Legal_exists *)
  (*
    Idea:
    use legal_exists to obtain s0 \in f.(distr)
    use forall_exists_Forall2_exists to obtain a list 'l' staisfying Forall2
    use sum_distr_exists to obtain final distr.

    pose exists final distr. and prove it.
  *)
  pose proof (Legal_exists f Hf) as [df Hdf].
  remember (fun (a : A) '(r, d0) =>
  r = df.(prob) a /\ d0 ∈ g a) as rel.
  assert (forall a: A, exists (rd: R * Distr B), rel a rd) as Hex_aux. {
    intros.
    specialize (Hg a).
    apply Legal_exists in Hg.
    destruct Hg as [d Hg].
    exists ((df.(prob) a), d).
    subst rel.
    split; [reflexivity | exact Hg].
  }
  pose proof (forall_exists_Forall2_exists rel df.(pset) Hex_aux) as [l Hl].
  specialize (ProbDistr_sum_distr_exists l) as [ds Hds]. (* key auxiliary theorem *)
  exists ds.
  sets_unfold.
  exists df, l.
  subst rel.
  split; [exact Hdf | ].
  split; [exact Hl | exact Hds].
- (* Legal_legal*)
  (*
    Idea:
    use ProbDistr_sum_distr_legal.
  *)
  exact HLegal_legal.
  
  - (* Legal_unique *)
    (* Idea:
      use ProbDistr_sum_distr_permutation_equiv
      use ProbDistr_sum_distr_equiv_equiv

      prove exists an intermediate l1'
        s.t. permutation l1 l1' and Forall2 equiv l1' l2.
    *)
    intros ds1 ds2 Hds1 Hds2. 

    assert (ProbDistr.legal ds1) as Hds1_legal by (apply HLegal_legal; exact Hds1).
    assert (ProbDistr.legal ds2) as Hds2_legal by (apply HLegal_legal; exact Hds2).

    destruct Hds1 as [df1 [l1 [Hdf1 [Hl1 Hsum_distr1]]]].
    destruct Hds2 as [df2 [l2 [Hdf2 [Hl2 Hsum_distr2]]]].
    specialize (Legal_unique f Hf df1 df2 Hdf1 Hdf2) as Hequiv_df1_df2.

    assert ( (* find intermediate l1'*) (* maybe reused later *)
      exists l1',
        Permutation l1 l1' /\
        Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) l1' l2
    ) as Hl1'_ex. {
      remember (fun (a : A) '(r, d) => r = df1.(prob) a /\ d ∈ g a) as rel.
      remember (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) as equiv.

      assert (
        forall (a : A) (rd1 rd2 : (R * Distr B)),
          rel a rd1
          -> rel a rd2
          -> equiv rd1 rd2
        ) as Hrel_equiv. {
        intros ? ? ? H1 H2.
        subst.
        destruct rd1 as [r1 d1].
        destruct rd2 as [r2 d2].
        split.
        - destruct H1 as [Hr1 _].
          destruct H2 as [Hr2 _].
          nra.
        - destruct H1 as [_ Hd1].
          destruct H2 as [_ Hd2].
          specialize (Legal_unique (g a) (Hg a) d1 d2 Hd1 Hd2) as Hequiv.
          exact Hequiv.
      }

      assert (
        Forall2 rel df2.(pset) l2        
      ) as Hl2'. {
        subst rel.
        clear Hsum_distr1 Hsum_distr2.
        induction Hl2 as [| x y lx_tail ly_tail].
        - constructor.
        - destruct y as [r d].
          destruct H as [Hr Hd].
          constructor.
          + split.
            * destruct Hequiv_df1_df2 as [Hprob _].
              rewrite (Hprob x).
              exact Hr.
            * exact Hd.
          + exact IHHl2.
      }

      assert (
        Equivalence equiv
      ) as Hequiv_equiv. {
        subst.
        split.
        - intros [r d].
          split; reflexivity.
        - intros [r1 d1] [r2 d2].
          intros [Hr1 Hd1].
          split; symmetry; tauto.
        - intros [r1 d1] [r2 d2] [r3 d3].
          intros [Hr12 Hd12] [Hr23 Hd23].
          split.
          + subst; reflexivity.
          + rewrite Hd12.
            rewrite Hd23.
            reflexivity. 
      }

      assert (
        forall a, exists b, rel a b
      ) as Hrel_ex. {
        intros.
        specialize (Legal_exists (g a) (Hg a)) as [d Hd].
        exists (df1.(prob) a, d).
        subst rel.
        split; [reflexivity | exact Hd].
      }

      destruct Hequiv_df1_df2 as [_ Hpset_perm].

      specialize (Permutation_Forall2_equiv_list_exists rel equiv df1.(pset) df2.(pset) l1 l2 Hrel_equiv Hrel_ex Hequiv_equiv Hpset_perm Hl1 Hl2') as Hl1'_ex.
      exact Hl1'_ex.
    }

    destruct Hl1'_ex as [l1' [Hperm_l1_l1' Hl1'_l2]].
    specialize (ProbDistr_sum_distr_exists l1') as [ds1' Hsum_distr1'].

    specialize (ProbDistr_sum_distr_equiv_equiv l1' l2 ds1' ds2 Hl1'_l2 Hsum_distr1' Hsum_distr2) as Hequiv1'2. (* key auxiliary lemma *)

    symmetry in Hequiv1'2.
    specialize (ProbDistr_equiv_legal_congr ds2 ds1' Hequiv1'2 Hds2_legal) as Hds1'_legal.
    destruct Hds1_legal as [_ _ Hds1_legal _].
    destruct Hds1'_legal as [_ _ Hds1'_legal _].

    specialize (ProbDistr_sum_distr_permutation_equiv l1 l1' ds1 ds1' Hperm_l1_l1' Hsum_distr1 Hsum_distr1' Hds1_legal Hds1'_legal) as Hequiv11'. (* key auxiliary lemma *)

    rewrite Hequiv11'.
    symmetry in Hequiv1'2.
    rewrite Hequiv1'2.
    reflexivity.
  - (* Legal_congr *)
    (* Idea:
      use ProbDistr_sum_distr_same_list_congr.
    *)
    intros ds1 ds2 Hequiv Hds1.
    destruct Hds1 as [df [l [Hdf [Hl Hsum_distr]]]].
    unfold __bind; sets_unfold.
    exists df.
    exists l.
    split; [exact Hdf |].
    split; [exact Hl |].
    apply ProbDistr_sum_distr_same_list_congr with (ds1:=ds1); assumption.
Qed.
(* Admitted. level 2? *)

    
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
Notation "x '.(Legal_congr)'" := (ProbMonad.Legal_congr _ x) (at level 1).

Definition Always {A: Type} (c: ProbMonad.M A) (P: A -> Prop): Prop :=
  Hoare (ProbMonad.compute_pr (res <- c;; ret (P res))) (fun pr => pr = 1%R).

  Lemma ProbMonad_compute_pr_unique:
  forall f r1 r2,
  ProbMonad.compute_pr f r1 -> 
  ProbMonad.compute_pr f r2 -> 
  r1 = r2.
Proof.
  intros.
  unfold ProbMonad.compute_pr in *.
  destruct H as [d1 [H1 H2]].
  destruct H0 as [d2 [H3 H4]].
  pose proof (f.(legal).(Legal_unique) d1 d2 H1 H3) as H_unique.
  apply ProbDistr_equiv_equiv_event in H_unique.
  unfold ProbDistr.equiv_event in H_unique.
  destruct H_unique as [r1' [r2' [H1' [H2' H_eq]]]].
  specialize (ProbDistr_compute_pr_unique d1 r1 r1' H2 H1') as H_unique1.
  specialize (ProbDistr_compute_pr_unique d2 r2 r2' H4 H2') as H_unique2.
  subst r1.
  subst r2.
  tauto.
Qed.

Lemma ProbMonad_compute_pr_exists:
  forall f, exists r, ProbMonad.compute_pr f r.
Proof.
  intros.
  unfold ProbMonad.compute_pr.
  pose proof f.(legal).(Legal_exists) as [d ?].
  pose proof ProbDistr_compute_pr_exists d as [r ?].
  exists r, d.
  tauto.
Qed.



Axiom decidable : forall (P: Prop), {P} + {~P}.

Definition sum_Prop {A: Type} (P: A -> Prop) (c: Distr A) : R :=
  sum (map (fun a => match decidable (P a) with
                     | left _ => c.(prob) a
                     | right _ => 0%R
                     end) c.(pset)).



Lemma sum_map_leq:
  forall (A : Type) (l : list A) (f g : A -> R),
    (forall x, In x l -> (f x <= g x)%R) ->
    (sum (map f l) <= sum (map g l))%R.
Proof.
  intros A l f g H.
  induction l as [| x xs IH].
  - simpl. lra.
  - simpl. apply Rplus_le_compat.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros y Hy. apply H. simpl. right. assumption.
Qed.

Lemma sum_Prop_imply:
  forall {A: Type} (P Q: A -> Prop) (f1 : Distr A) (c: ProbMonad.M A),
    (forall a, P a -> Q a) -> f1 ∈ c.(distr) ->
    (sum_Prop P f1 <= sum_Prop Q f1)%R.
Proof.
  intros.
  unfold sum_Prop.
  apply sum_map_leq.
  intros.
  destruct (decidable (P x)).
  + destruct (decidable (Q x)).
    * lra.
    * exfalso. apply n. apply H. assumption.
  + destruct (decidable (Q x)).
    * pose proof c.(legal).(Legal_legal) as H_legal.
      specialize (H_legal f1 H0).
      destruct H_legal as [_ ? _ _].
      specialize (legal_nonneg x).
      lra.
    * lra.
Qed.

Lemma sum_ge_0: forall (A: Type) (l: list A) (f: A -> R),
  (forall x, (f x >= 0)%R) ->
  (0 <= sum (map f l))%R.
Proof.
  intros A l f H.
  induction l.
  - simpl. lra.
  - simpl.
    specialize (H a).
    lra.
Qed.

Lemma sum_app: forall (l1 l2: list R),
  (sum (l1 ++ l2) = sum l1 + sum l2)%R.
Proof.
  intros.
  induction l1.
  - simpl. lra.
  - simpl. rewrite IHl1. lra.
Qed.

Lemma sum_cons: forall (x: R) (l: list R),
  sum (x :: l) = (x + sum l)%R.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma sum_subset_leq:
  forall (A:Type) (l1 l2:list A) (f: A ->R), 
    (forall x, In x l1 -> In x l2) -> (* l1 is subset of l2 *)(forall x, (f x >= 0)%R) ->
    NoDup l1 ->
    NoDup l2 ->
    (sum (map f l1) <= sum(map f l2))%R.
Proof.
  intros ? ? ? ? Hin_imply Hnonneg.
  intros HNoDup1 HNoDup2.
  (* Define a boolean membership test function *)
  assert (forall l, exists in_test : A -> bool,
    forall x, In x l <-> in_test x = true) as Hin_test_ex.
  {
    intro l.
    exists (fun x => if In_dec eq_dec x l then true else false).
    intros x.
    destruct (In_dec eq_dec x l); split; intro H; try discriminate; auto.
  }

  assert (forall (l: list A) (in_test : A->bool),
    (sum (map f (filter in_test l)) <= sum (map f l))%R
  ) as H_filter_le. {
    clear dependent l1.
    clear dependent l2.
    intros l in_test.
    induction l as [| head ltail IH]; simpl.
    - nra.
    - destruct (classic (in_test head = true)) as [H_in | H_nin].
      + rewrite H_in.
        simpl.
        nra.
      + assert (in_test head = false) as H_nin'. {
          destruct (in_test head).
          - contradiction.
          - reflexivity.
        }
        rewrite H_nin'.
        specialize (Hnonneg head).
        nra.
  }

  destruct (Hin_test_ex l1) as [in_test Hin_test].
  specialize H_filter_le with (l:=l2) (in_test:=in_test) as H_filter_le.
  assert (Permutation l1 (filter in_test l2)) as Hperm. {
    apply NoDup_Permutation; [exact HNoDup1 | apply NoDup_filter; exact HNoDup2 |].
    intro x.
    split; intro.
    - apply filter_In.
      apply Hin_imply in H as H'.
      rewrite <-Hin_test.
      split; assumption.
    - apply filter_In in H as [_ H'].
      rewrite Hin_test.
      exact H'.
  }

  assert (forall x, f x = f x) as Hf_refl by (trivial).

  specialize (Permutation_sum_map_eq l1 (filter in_test l2) f f Hperm Hf_refl) as H_rewrite.
  rewrite H_rewrite.
  exact H_filter_le.
Qed.


Lemma ProbMonad_compute_pr_less_than_one: forall (f : ProbMonad.M Prop) (r: R),
  ProbMonad.compute_pr f r -> (r <= 1)%R.
Proof.
  intros f r H.
  unfold ProbMonad.compute_pr in H.
  destruct H as [d [Hd Hpr]].
  
  (* Use Legal_legal to show d is legal *)
  pose proof (f.(legal).(Legal_legal) d Hd) as Hlegal.
  
  destruct Hlegal as [Hlegal1 Hlegal2 Hlegal3 Hlegal4].
  destruct Hpr as [l [Hnodup [Hin_equiv Hsum]]].
  rewrite <- Hsum.
  
  (* Show sum_prob l d.(prob) <= sum (map d.(prob) d.(pset)) *)
  unfold sum_prob in *.
  apply Rle_trans with (r2 := sum (map d.(prob) d.(pset))).
  - (* First show the sum over l is <= sum over d.(pset) *)
    assert (forall x, In x l -> In x d.(pset)) as Hsubset.
    { intros x Hinl.
      apply Hin_equiv in Hinl.
      tauto. }
    apply (sum_subset_leq _ l d.(pset) d.(prob)).
    intros x Hinx.
    + (* Show all elements in l are in d.(pset) *)
      specialize (Hsubset x).
      simpl.
      apply Hsubset.
      exact Hinx.
    + (* Show all probabilities are non-negative *)
      exact Hlegal2.
    + exact Hnodup. 
    + exact Hlegal1.
  - (* Then use Hlegal4 to show total sum is 1 *)
    rewrite Hlegal4.
    lra.
Qed.

Lemma compute_pr_sum_Prop:
  forall {A: Type} (P: A -> Prop)(c: ProbMonad.M A) (f: Distr A)(d: R),
    d ∈ ProbMonad.compute_pr (res <- c;; ret (P res)) -> f ∈ c.(distr)->
    d = sum_Prop P f.
Proof.
Admitted.

Lemma ProbMonad_compute_pr_imply: forall {A: Type} (P Q: A -> Prop) (c: ProbMonad.M A) (e d: R),
  (forall a, P a -> Q a) ->
  (d ∈ ProbMonad.compute_pr(res <- c;; ret (P res))) ->
  (e ∈ ProbMonad.compute_pr(res <- c;; ret (Q res))) -> ((e >= d)%R).
Proof.
  intros.
  specialize (compute_pr_sum_Prop P) as H2.
  specialize (compute_pr_sum_Prop Q) as H3.
  pose proof c.(legal) as H_legal.
  destruct H_legal as [H_legal1 _ _ _].
  destruct H_legal1 as [d1 H_legal1].
  specialize (H2 c d1 d).
  specialize (H3 c d1 e).
  specialize (H2 H0 H_legal1 ).
  specialize (H3 H1 H_legal1).
  apply sum_Prop_imply with (P:=P) (Q:=Q) (f1:=d1) (c:=c) in H.
  + lra.
  + exact H_legal1.
Qed.
Lemma eq_to_ineq :
  forall a : R,
   (a >= 1)%R -> (a <= 1)%R -> a = 1%R.
Proof.
  intros.
  lra.
Qed.

Theorem Always_conseq: forall {A: Type} (P Q: A -> Prop),
  (forall a, P a -> Q a) ->
  (forall c, Always c P -> Always c Q).
Proof.
  intros.
  unfold Always in *.
  unfold Hoare in *.
  intros.
  apply eq_to_ineq.
  2:{
    apply ProbMonad_compute_pr_less_than_one with (f:=res <- c;; ret (Q res)).
    exact H1.
  }
  - pose proof ProbMonad_compute_pr_exists as H9.
    specialize (H9 (res <- c;; ret (P res))) as [r H8].
    specialize (H0 r).
    specialize (H0 H8).
    pose proof ProbMonad_compute_pr_imply(A:=A).
    specialize (H2 P Q c a r).
    specialize (H2 H H8 H1).
    rewrite H0 in H2.
    exact H2.
Qed.

(** The Lemma or Theorem in level3 is helpful to prove Theorem Always_bind_ret,
so the proof of it is right after the proof of Lemma bind_ret_l_event **)

(** Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
 **)

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
    ProbMonad verson of ProbDistr_compute_pr_unique.
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

(**
  Description:
    ProbMonad.equiv_event is indeed an Equivalence relation.
*)
#[export] Instance ProbMonad_equiv_event_equiv:
  Equivalence ProbMonad.equiv_event.
Proof.
  unfold ProbMonad.equiv_event.
  split.
  - unfold Reflexive.
    intros x.
    destruct (ProbMonad.Legal_exists _ x.(legal)) as [d1 ?].
    exists d1, d1.
    split.
    + exact H.
    + split.
      * exact H.
      * apply ProbDistr_equiv_equiv_event.
        apply x.(legal).(Legal_unique).
        -- exact H.
        -- exact H.
  - unfold Symmetric.
    intros x y H.
    destruct H as [r1 [r2 [H1 [H2 H3]]]].
    exists r2, r1.
    split.
    + exact H2.
    + split.
      * exact H1.
      * apply ProbDistr_equiv_event_equiv.
        exact H3.
  - unfold Transitive.
    intros x y z H1 H2.
    destruct H1 as [d1 [d2 [H_d1 [H_d2 H_equiv_d1_d2]]]].
    destruct H2 as [d2' [d3 [H_d2' [H_d3 H_equiv_d2'_d3]]]].
    exists d1, d3.
    split.
    + exact H_d1.
    + split.
      * exact H_d3.
      * assert (H_equiv_d2_d2': ProbDistr.equiv_event d2 d2').
        {
          pose proof (y.(legal).(Legal_unique) d2 d2' H_d2 H_d2') as H_equiv.
          apply ProbDistr_equiv_equiv_event.
          exact H_equiv.
        }
        unfold ProbDistr.equiv_event in H_equiv_d1_d2, H_equiv_d2'_d3, H_equiv_d2_d2'.
        destruct H_equiv_d1_d2 as [r1 [r2 [H_r1 [H_r2 H_equiv_r1_r2]]]].
        destruct H_equiv_d2_d2' as [r3 [r4 [H_r3 [H_r4 H_equiv_r3_r4]]]].
        destruct H_equiv_d2'_d3 as [r5 [r6 [H_r5 [H_r6 H_equiv_r5_r6]]]].
        unfold ProbDistr.equiv_event.
        exists r1, r6.
        specialize (ProbDistr_compute_pr_unique d2 r2 r3 H_r2 H_r3) as H_equiv_r2_r3.
        specialize (ProbDistr_compute_pr_unique d2' r4 r5 H_r4 H_r5) as H_equiv_r4_r5.
        split.
        -- exact H_r1.
        -- split.
           ++ exact H_r6.
           ++ rewrite H_equiv_r1_r2, H_equiv_r2_r3, H_equiv_r3_r4, H_equiv_r4_r5, H_equiv_r5_r6.
              reflexivity.
Qed.
(** Admitted.  Level 2 *)

(**
  Name: ProbDistr_equiv_event_congr
  Property: Auxiliary Theorem
  Description:
    simplify transistive realtion on ProbDistr.equiv_event.
*)
Lemma ProbDistr_equiv_event_congr :
  forall (d1 d2 d3 : Distr Prop),
    ProbDistr.equiv_event d1 d2 ->
    ProbDistr.equiv_event d2 d3 ->
    ProbDistr.equiv_event d1 d3.
Proof.
  intros.
  transitivity d2.
  - exact H.
  - exact H0.
Qed.

(**
  Description:
    ProbMonad.imply_event is preserved under ProbMonad.equiv_event.
    eg: x==y /\ x0==y0 -> (ProbMonad.imply_event x x0 <-> ProbMonad.imply_event y y0)
*)
#[export] Instance ProbMonad_imply_event_congr:
  Proper (ProbMonad.equiv_event ==>
          ProbMonad.equiv_event ==> iff) ProbMonad.imply_event.
Proof.
  unfold Proper, respectful.
  intros.
  destruct H as [d1 [d2 [H_d1 [H_d2 H_equiv_d1_d2]]]].
  destruct H0 as [d3 [d4 [H_d3 [H_d4 H_equiv_d3_d4]]]].
  split; intros; unfold ProbMonad.imply_event in *; destruct H as [d5 [d6 [H_d5 [H_d6 H_impl]]]].
  - exists d2, d4.
    repeat split.
    + exact H_d2.
    + exact H_d4.
    + assert (H_equiv_d1_d5: ProbDistr.equiv_event d1 d5).
      {
        pose proof (x.(legal).(Legal_unique) d1 d5 H_d1 H_d5) as H_equiv.
        apply ProbDistr_equiv_equiv_event.
        exact H_equiv.
      }
      assert (H_equiv_d3_d6: ProbDistr.equiv_event d3 d6).
      {
        pose proof (x0.(legal).(Legal_unique) d3 d6 H_d3 H_d6) as H_equiv.
        apply ProbDistr_equiv_equiv_event.
        exact H_equiv.
      }
      apply ProbDistr_equiv_event_equiv in H_equiv_d1_d2, H_equiv_d3_d6.
      specialize (ProbDistr_equiv_event_congr d2 d1 d5 H_equiv_d1_d2 H_equiv_d1_d5) as H_equiv_d2_d5.
      specialize (ProbDistr_equiv_event_congr d6 d3 d4 H_equiv_d3_d6 H_equiv_d3_d4) as H_equiv_d6_d4.
      clear H_equiv_d1_d2 H_equiv_d3_d6 H_equiv_d3_d4.
      destruct H_equiv_d2_d5 as [r1 [r2 [H_r1 [H_r2 H_equiv_r1_r2]]]].
      destruct H_equiv_d6_d4 as [r3 [r4 [H_r3 [H_r4 H_equiv_r3_r4]]]].
      destruct H_impl as [r5 [r6 [H_r5 [H_r6 H_impl]]]].
      specialize (ProbDistr_compute_pr_unique d5 r2 r5 H_r2 H_r5) as H_equiv_r2_r5.
      specialize (ProbDistr_compute_pr_unique d6 r3 r6 H_r3 H_r6) as H_equiv_r3_r6.
      unfold ProbDistr.imply_event.
      exists r1, r4.
      repeat split.
      * exact H_r1.
      * exact H_r4.
      * rewrite H_equiv_r1_r2, H_equiv_r2_r5, <- H_equiv_r3_r4, H_equiv_r3_r6.
        exact H_impl.
  - exists d1, d3.
    repeat split.
    + exact H_d1.
    + exact H_d3.
    + assert (H_equiv_d2_d5: ProbDistr.equiv_event d2 d5).
      {
        pose proof (y.(legal).(Legal_unique) d2 d5 H_d2 H_d5) as H_equiv.
        apply ProbDistr_equiv_equiv_event.
        exact H_equiv.
      }
      assert (H_equiv_d4_d6: ProbDistr.equiv_event d4 d6).
      {
        pose proof (y0.(legal).(Legal_unique) d4 d6 H_d4 H_d6) as H_equiv.
        apply ProbDistr_equiv_equiv_event.
        exact H_equiv.
      }
      specialize (ProbDistr_equiv_event_congr d1 d2 d5 H_equiv_d1_d2 H_equiv_d2_d5) as H_equiv_d1_d5.
      specialize (ProbDistr_equiv_event_congr d3 d4 d6 H_equiv_d3_d4 H_equiv_d4_d6) as H_equiv_d3_d6.
      clear H_equiv_d2_d5 H_equiv_d4_d6 H_equiv_d3_d4 H_equiv_d1_d2.
      destruct H_equiv_d1_d5 as [r1 [r2 [H_r1 [H_r2 H_equiv_r1_r2]]]].
      destruct H_equiv_d3_d6 as [r3 [r4 [H_r3 [H_r4 H_equiv_r3_r4]]]].
      destruct H_impl as [r5 [r6 [H_r5 [H_r6 H_impl]]]].
      specialize (ProbDistr_compute_pr_unique d5 r2 r5 H_r2 H_r5) as H_equiv_r2_r5.
      specialize (ProbDistr_compute_pr_unique d6 r4 r6 H_r4 H_r6) as H_equiv_r4_r6.
      unfold ProbDistr.imply_event.
      exists r1, r3.
      repeat split.
      * exact H_r1.
      * exact H_r3.
      * rewrite H_equiv_r1_r2, H_equiv_r2_r5, H_equiv_r3_r4, H_equiv_r4_r6.
        exact H_impl.
Qed.
(** Admitted.  Level 2 *)

(**
  Description:
    ProbMonad.compute_pr is congruence under ProbMonad.equiv_event.
    eg: x==y -> ProbMonad.compute_pr x = ProbMonad.compute_pr y
*)
#[export] Instance compute_pr_congr:
  Proper (ProbMonad.equiv_event ==> Sets.equiv) ProbMonad.compute_pr.
Proof.
  unfold Proper, respectful.
  intros.
  destruct H as [d1 [d2 [H_d1 [H_d2 H_equiv_d1_d2]]]].
  split; intros; unfold ProbMonad.compute_pr in *; destruct H as [d3 [H_d3 H_pr_d3]].
  - assert (H_equiv_d1_d3: ProbDistr.equiv_event d1 d3).
    {
      pose proof (x.(legal).(Legal_unique) d1 d3 H_d1 H_d3) as H_equiv.
      apply ProbDistr_equiv_equiv_event.
      exact H_equiv.
    }
    exists d2.
    split.
    + exact H_d2.
    + destruct H_equiv_d1_d3 as [r1 [r2 [H_r1 [H_r2 H_equiv_r1_r2]]]].
      destruct H_equiv_d1_d2 as [r3 [r4 [H_r3 [H_r4 H_equiv_r3_r4]]]].
      specialize (ProbDistr_compute_pr_unique d3 a r2 H_pr_d3 H_r2) as H_equiv_a_r2.
      specialize (ProbDistr_compute_pr_unique d1 r1 r3 H_r1 H_r3) as H_equiv_r1_r3.
      rewrite H_equiv_a_r2, <- H_equiv_r1_r2, H_equiv_r1_r3, H_equiv_r3_r4.
      exact H_r4.
  - assert (H_equiv_d2_d3: ProbDistr.equiv_event d2 d3).
    {
      pose proof (y.(legal).(Legal_unique) d2 d3 H_d2 H_d3) as H_equiv.
      apply ProbDistr_equiv_equiv_event.
      exact H_equiv.
    }
    exists d1.
    split.
    + exact H_d1.
    + destruct H_equiv_d2_d3 as [r1 [r2 [H_r1 [H_r2 H_equiv_r1_r2]]]].
      destruct H_equiv_d1_d2 as [r3 [r4 [H_r3 [H_r4 H_equiv_r3_r4]]]].
      specialize (ProbDistr_compute_pr_unique d3 a r2 H_pr_d3 H_r2) as H_equiv_a_r2.
      specialize (ProbDistr_compute_pr_unique d2 r1 r4 H_r1 H_r4) as H_equiv_r1_r4.
      rewrite H_equiv_a_r2, <- H_equiv_r1_r2, H_equiv_r1_r4, <- H_equiv_r3_r4.
      exact H_r3.
Qed. 
(**Admitted.  Level 2 *)

(*
  Description:
    the imply_event relation can imply the montonicity of compute_pr relation.
*)
Theorem compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbMonad.compute_pr f1 r1 ->
    ProbMonad.compute_pr f2 r2 ->
    ProbMonad.imply_event f1 f2 ->
    (r1 <= r2)%R.
Proof.
    intros f1 f2 r1 r2 Hpr1 Hpr2 Himpl.
    unfold ProbMonad.compute_pr in *.
    destruct Hpr1 as [d1 [Hf1 Hd1]].
    destruct Hpr2 as [d2 [Hf2 Hd2]].
    destruct Himpl as [d1' [d2' [Hd1' [Hd2' Himpl']]]].
    assert (Himpl_eq:ProbDistr.equiv d1 d1').
    {
      apply f1.(legal).(Legal_unique).
      exact Hf1.
      exact Hd1'.
    }
    assert (Himpl_eq':ProbDistr.equiv d2 d2').
    {
      apply f2.(legal).(Legal_unique).
      exact Hf2.
      exact Hd2'.
    }
    specialize (ProbDistr_equiv_equiv_event d1 d1' Himpl_eq) as Himpl_eq_event.
    specialize (ProbDistr_equiv_equiv_event d2 d2' Himpl_eq') as Himpl_eq_event'.
    specialize (ProbDistr_imply_event_congr d1 d1' Himpl_eq_event d2 d2' Himpl_eq_event') as Himpl_eq_event_congr.
    apply Himpl_eq_event_congr in Himpl'.
    unfold ProbDistr.imply_event in Himpl'.
    specialize (ProbDistr_compute_pr_mono d1 d2 r1 r2 Hd1 Hd2 Himpl') as Hmono.
    exact Hmono.
Qed.



(* 
  Auxiliary Theorem:
    Apply forall a:A, g1 a == g2 a into
      a Forall2 form.
*)
Lemma Forall2_equiv_g1_g2:
  forall (A B : Type) (d1 : Distr A) (d2 : list (R * Distr B)) (g1 g2 : A -> ProbMonad.M B),
    (forall a : A, g1 a == g2 a) ->
    Forall2 (fun (a : A) '(r, d) => r = d1.(prob) a /\ d ∈ (g1 a).(distr)) d1.(pset) d2 ->
    Forall2 (fun (a0 : A) '(r, d) => r = d1.(prob) a0 /\ d ∈ (g2 a0).(distr)) d1.(pset) d2.
Proof.
  intros A B d1 d2 g1 g2 H2 H4.
  induction H4.
  - (* Base case: empty list *)
    constructor.
  - (* Inductive case *)
    destruct y as [r d].
    constructor.
    + (* Prove the head of the list *)
      destruct H as [Hr Hd].
      split.
      * exact Hr.
      * apply H2 in Hd. exact Hd.
    + (* Prove the tail of the list *)
      apply IHForall2.
Qed.


(* 
  Description:
    `bind` operation respects the `equiv` equivalence relation. 
    Specifically, if two monad `f1` and `f2` are equivalent, 
    and for all elements `a` of type `A`, the monadic values `g1 a` and `g2 a` are equivalent, 
    then the result of binding `f1` with `g1` is equivalent to the result of binding `f2` with `g2`.
    
    Formally, if `f1 == f2` and `(forall a, g1 a == g2 a)`, then `bind f1 g1 == bind f2 g2`.
*)
#[export] Instance ProbMonad_bind_congr (A B: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv ==>
          ProbMonad.equiv)
    (@bind _ ProbMonad A B).
Proof.
  unfold Proper, pointwise_relation.
  intros f1 f2 H1 g1 g2 H2.
  unfold ProbMonad.equiv.
  split.
  - intros.
    unfold ProbMonad.__bind in *.
    destruct H as [d1 [d2 [H3 [H4 H5]]]].
    exists d1, d2.
    split.
    + apply H1.
      exact H3.
    + split.
      * specialize (Forall2_equiv_g1_g2 _ _ d1 _ g1 g2 H2 H4) as H6.
        exact H6.
      * exact H5.
  - intros.
    unfold ProbMonad.__bind in *.
    destruct H as [d1 [d2 [H3 [H4 H5]]]].
    exists d1, d2.
    split.
    + apply H1.
      exact H3.
    + split.
      * assert (forall a: A, g2 a == g1 a) as H2'.
        {
          intros.
          symmetry.
          apply H2.
        }
        specialize (Forall2_equiv_g1_g2 _ _ d1 _ g2 g1 H2' H4) as H6.
        exact H6.
      * exact H5. 
Qed.    

Theorem Forall2_imply_event_sum_distr_imply_event:
  forall (L1 L2 : list (R * Distr Prop)) (ds1 ds2 : Distr Prop),
     Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.imply_event d1 d2) L1 L2
  -> ProbDistr.sum_distr L1 ds1 
  -> ProbDistr.sum_distr L2 ds2
  -> ProbDistr.imply_event ds1 ds2.
Proof.
  intros L1 L2 ds1 ds2 H_Forall2 H_sum1 H_sum2.
  unfold ProbDistr.imply_event in *.
  
  induction H_Forall2.
  
  - (* Base Case: L1 = [], L2 = [] *)
    admit. 

  - (* Inductive Step: L1 = (r1, d1) :: L1', L2 = (r2, d2) :: L2' *)
    intros.
    destruct x as [r1 d1].
    destruct y as [r2 d2].
    simpl in *.
    destruct H as [Hr_eq Himpl_event].
    subst r2.

    (* Get compute_pr values for d1 and d2 *)
    destruct Himpl_event as [p1 [p2 [Hp1 [Hp2 Hp_le]]]].

    (* Get compute_pr values for ds1' and ds2' from IH *)
    destruct H_sum1 as [H_nodup1 [H_in1 H_sum1]].
    destruct H_sum2 as [H_nodup2 [H_in2 H_sum2]].

Admitted.

(*
  Name: Permutation_concat_map_in_equiv
  Property: Auxiliary Theorem
  Description:
    Permutation L1 L2 -> In (concat (map f L1) <-> In (concat (map f L2))
*)
Lemma Permutation_concat_map_in_equiv :
  forall (A B : Type) (f : A -> list B) (L1 L2 : list A) (x : B),
    Permutation L1 L2 ->
    (In x (concat (map f L1)) <-> In x (concat (map f L2))).
Proof.
  intros A B f L1 L2 x Hperm.
  apply Permutation_map with (f := f) in Hperm.
  rewrite <-Hperm.
  reflexivity.
Qed.

Lemma Forall2_length: forall {A B} (R: A -> B -> Prop) l1 l2,
  Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  intros A B R l1 l2 H.
  induction H.
  - reflexivity. 
  - simpl.
    f_equal.
    exact IHForall2.
Qed.

Lemma Forall2_in_right {A B} (R: A -> B -> Prop) (x: A) (l1: list A) (l2: list B) (b: B):
  Forall2 R l1 l2 -> In b l2 -> exists a, In a l1 /\ R a b.
Proof.
  intros H Hin.
  induction H.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin.
    + exists x0.
      split.
      * left.
        reflexivity.
      * rewrite <- H1.
        exact H.
    + apply IHForall2 in H1 as HH.
      destruct HH as [a [Ha HR]].
      exists a.
      split; [right; exact Ha | exact HR].
Qed.

Lemma Forall2_in_left {A B} (R: A -> B -> Prop) (a: A) (l1: list A) (l2: list B):
  Forall2 R l1 l2 -> In a l1 -> exists b, In b l2 /\ R a b.
Proof.
  intros H Hin.
  induction H.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + exists y.
      split.
      * left.
        reflexivity.
      * rewrite <- Heq.
        exact H.
    + apply IHForall2 in Hin' as HH.
      destruct HH as [b [Hb HR]].
      exists b.
      split; [right; exact Hb | exact HR].
Qed.

Theorem ProbDistr_sum_distr_legal_precondition_helper_MonadVer:
  forall {A B: Type} (f : ProbMonad.M A) (g: A -> ProbMonad.M B) (df : Distr A) (l : list (R * Distr B)),
  df ∈ f.(distr) ->
  Forall2 (fun (a : A) '(r, d) => r = df.(prob) a /\ d ∈ (g a).(distr)) df.(pset) l ->
  Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l /\
  sum (map (fun '(r, d) => r) l) = 1%R.
Proof.
  intros ? ? ? ? ? ? Hdf Hl.
  specialize f.(legal) as Hf.
  remember (fun x => (g x).(legal)) as Hg.
  split.
  * induction Hl as [| x y lx_tail ly_tail].
    - constructor.
    - destruct y as [r d].
      destruct H as [Hr Hd].
      constructor.
      + destruct Hf as [_ Hdf_legal _ _].
        specialize (Hdf_legal df Hdf).
        pose proof (ProbDistr.legal_nonneg df Hdf_legal) as H_ge0.
        specialize (H_ge0 x).
        subst r.
        
        destruct (Hg x) as [_ Hd_legal _ _].
        specialize (Hd_legal d Hd).
        tauto.
      + exact IHHl.
  * assert ( (* summation r = 1, prerequisite for ProbDistr_sum_distr_legal *)
      sum (map (fun '(r, d) => r) l) = 1%R
    ) as Hsum_r. {
      assert (sum (map (fun '(r, d) => r) l) = sum (map (df.(prob)) df.(pset))) as H_aux.
      {
        induction Hl as [| x [r d] lx_tail ly_tail [Hr Hd] Htail]; simpl.
        - reflexivity.
        - rewrite IHHtail.
          rewrite <-Hr.
          reflexivity.    
      }
      rewrite H_aux.
      destruct Hf as [_ Hdf_legal _ _].
      specialize (Hdf_legal df Hdf).
      destruct Hdf_legal as [_ _ _ Hsum_prob1].
      unfold sum_prob in Hsum_prob1.
      exact Hsum_prob1.
    }
    apply Hsum_r.
Qed.


(*
  Name: bind_congr_aux
  Property: Auxiliary Theorem
  Description:
    If two distributions are equivalent and mapped by the same function g,
    then their sum_distr results are also equivalent.
*)
Lemma bind_congr_aux: (* change prop to general type B*)
  forall {A B : Type} (dx dy: Distr A) (f : ProbMonad.M A) (g: A -> ProbMonad.M B) 
         (lx ly: list (R * Distr B)) (dsx dsy: Distr B),
    dx ∈ f.(distr) ->
    dy ∈ f.(distr) ->
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (g a).(distr)) dx.(pset) lx ->
    Forall2 (fun a '(r, d) => r = dy.(prob) a /\ d ∈ (g a).(distr)) dy.(pset) ly ->
    ProbDistr.sum_distr lx dsx ->
    ProbDistr.sum_distr ly dsy ->
    ProbDistr.equiv dsx dsy.
Proof.
  (* almost the same as __bind_legal Legal_unique *)
  intros A B df1 df2 f g l1 l2 ds1 ds2 Hdf1 Hdf2 Hl1 Hl2 Hsum_distr1 Hsum_distr2.

  pose proof (f.(legal).(Legal_unique) df1 df2 Hdf1 Hdf2) as Hequiv_df1_df2.
  assert (forall a, ProbMonad.Legal (g a).(distr)) as Hg.
  {
    intros.
    apply (g a).(legal).
  }

  assert ( (* find intermediate l1'*) (* maybe reused later *)
    exists l1',
      Permutation l1 l1' /\
      Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) l1' l2
  ) as Hl1'_ex. {
    remember (fun (a : A) '(r, d) => r = df1.(prob) a /\ d ∈ (g a).(distr)) as rel.
    remember (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) as equiv.

    assert (
      forall (a : A) (rd1 rd2 : (R * Distr B)),
        rel a rd1
        -> rel a rd2
        -> equiv rd1 rd2
      ) as Hrel_equiv. {
      intros ? ? ? H1 H2.
      subst.
      destruct rd1 as [r1 d1].
      destruct rd2 as [r2 d2].
      split.
      - destruct H1 as [Hr1 _].
        destruct H2 as [Hr2 _].
        nra.
      - destruct H1 as [_ Hd1].
        destruct H2 as [_ Hd2].
        specialize ((g a).(legal).(Legal_unique) d1 d2 Hd1 Hd2) as Hequiv.
        exact Hequiv.
    }

    assert (
      Forall2 rel df2.(pset) l2        
    ) as Hl2'. {
      subst rel.
      clear Hsum_distr1 Hsum_distr2.
      induction Hl2 as [| x y lx_tail ly_tail].
      - constructor.
      - destruct y as [r d].
        destruct H as [Hr Hd].
        constructor.
        + split.
          * destruct Hequiv_df1_df2 as [Hprob _].
            rewrite (Hprob x).
            exact Hr.
          * exact Hd.
        + exact IHHl2.
    }

    assert (
      Equivalence equiv
    ) as Hequiv_equiv. {
      subst.
      split.
      - intros [r d].
        split; reflexivity.
      - intros [r1 d1] [r2 d2].
        intros [Hr1 Hd1].
        split; symmetry; tauto.
      - intros [r1 d1] [r2 d2] [r3 d3].
        intros [Hr12 Hd12] [Hr23 Hd23].
        split.
        + subst; reflexivity.
        + rewrite Hd12.
          rewrite Hd23.
          reflexivity. 
    }

    assert (
      forall a, exists b, rel a b
    ) as Hrel_ex. {
      intros.
      specialize ((g a).(legal).(Legal_exists)) as [d Hd].
      exists (df1.(prob) a, d).
      subst rel.
      split; [reflexivity | exact Hd].
    }

    destruct Hequiv_df1_df2 as [_ Hpset_perm].

    specialize (Permutation_Forall2_equiv_list_exists rel equiv df1.(pset) df2.(pset) l1 l2 Hrel_equiv Hrel_ex Hequiv_equiv Hpset_perm Hl1 Hl2') as Hl1'_ex.
    exact Hl1'_ex.
  }

  destruct Hl1'_ex as [l1' [Hperm_l1_l1' Hl1'_l2]].
  specialize (ProbDistr_sum_distr_exists l1') as [ds1' Hsum_distr1'].

  specialize (ProbDistr_sum_distr_equiv_equiv l1' l2 ds1' ds2 Hl1'_l2 Hsum_distr1' Hsum_distr2) as Hequiv1'2. (* key auxiliary lemma *)

  (* difference. we need to retrive ds1, ds1' legality via sum_distr_legal *)
  specialize (ProbMonad.ProbDistr_sum_distr_legal_precondition_helper_MonadVer f g df1 l1 Hdf1 Hl1) as [Hhelper1a Hhelper1b].

  pose proof (ProbDistr_sum_distr_legal l1 ds1 Hhelper1a Hhelper1b Hsum_distr1) as Hds1_legal.

  specialize (ProbMonad.ProbDistr_sum_distr_legal_precondition_helper_MonadVer f g df2 l2 Hdf2 Hl2) as [Hhelper2a Hhelper2b].

  pose proof (ProbDistr_sum_distr_legal l2 ds2 Hhelper2a Hhelper2b Hsum_distr2) as Hds2_legal.

  symmetry in Hequiv1'2.
  specialize (ProbDistr_equiv_legal_congr ds2 ds1' Hequiv1'2 Hds2_legal) as Hds1'_legal.

  destruct Hds1_legal as [_ _ Hds1_legal _].
  destruct Hds1'_legal as [_ _ Hds1'_legal _].

  specialize (ProbDistr_sum_distr_permutation_equiv l1 l1' ds1 ds1' Hperm_l1_l1' Hsum_distr1 Hsum_distr1' Hds1_legal Hds1'_legal) as Hequiv11'. (* key auxiliary lemma *)

  rewrite Hequiv11'.
  rewrite Hequiv1'2.
  reflexivity.
Qed.

Lemma Forall2_imply_congr:
  forall {A B: Type} (l1: list A) (l2: list B) (P Q: A -> B -> Prop) ,
    Forall2 P l1 l2 ->
    (forall a b, 
      In a l1 -> In b l2 -> P a b -> Q a b) ->
    Forall2 Q l1 l2.
Proof.
  intros A B l1 l2  P Q H_forall2 H_imply.
  induction H_forall2.
  - constructor.
  - constructor.
    + apply H_imply.
      1,2,3:simpl; auto.
    + apply IHH_forall2.
      intros.
      apply H_imply.
      1,2,3: simpl; auto.
Qed.

(*
  Name: Forall2_pointwise_mono_aux
  Property: Auxiliary Theorem
  Description:
    If gx <= gy pointwise, then applying them to the same distribution dx
    results in lists that are related by imply_event pointwise.
*)
Lemma Forall2_pointwise_mono_aux:
  forall (A: Type) (dx: Distr A) (gx gy: A -> ProbMonad.M Prop)
         (lx ly: list (R * Distr Prop)),
    (forall a, ProbMonad.imply_event (gx a) (gy a)) ->
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (gx a).(distr)) dx.(pset) lx ->
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (gy a).(distr)) dx.(pset) ly ->
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.imply_event d1 d2) lx ly.
Proof.
  intros A dx gx gy lx ly H_mono H_lx H_ly.
  (* Do induction on both Forall2 relations simultaneously *)
  revert ly H_ly.
  induction H_lx; intros.
  
  - (* Base case: empty lists *)
    inversion H_ly.
    constructor.
    
  - (* Inductive case *)
    inversion H_ly; subst.
    constructor.
    + (* Prove head elements are related *)
      destruct y0 as [r2 d2].
      destruct y as [r1 d1].
      destruct H as [Hr1 Hd1].
      destruct H2 as [Hr2 Hd2].
      split.
      * (* Show r1 = r2 *)
        rewrite Hr1, Hr2.
        reflexivity.
      * (* Show ProbDistr.imply_event d1 d2 *)
        specialize (H_mono x).
        unfold ProbMonad.imply_event in H_mono.
        destruct H_mono as [d1' [d2' [Hd1' [Hd2' H_impl]]]].
        (* Use Legal_unique to show d1 = d1' and d2 = d2' *)
        pose proof ((gx x).(legal).(Legal_unique) d1 d1' Hd1 Hd1') as H_eq1.
        pose proof ((gy x).(legal).(Legal_unique) d2 d2' Hd2 Hd2') as H_eq2.
        (* Use equiv to show imply_event preserves under equiv *)
        apply ProbDistr_equiv_equiv_event in H_eq1.
        apply ProbDistr_equiv_equiv_event in H_eq2.
        apply ProbDistr_imply_event_congr with d1' d2'; 
          [exact H_eq1 | exact H_eq2 | exact H_impl].
          
    + (* Apply IH to handle tail *)
      apply IHH_lx.
      exact H4.
Qed.

(*
  Description:
    bind operation preserves the imply_event relation 
    when the first argument is equivalent and the second argument is monotonic.
*)

#[export] Instance ProbMonad_bind_mono_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.imply_event ==>
          ProbMonad.imply_event)
    (@bind _ ProbMonad A Prop).
Proof.
  unfold Proper, respectful.
  intros fx fy H_eq_f gx gy H_eq_g.
  unfold ProbMonad.imply_event.
  simpl.
  unfold ProbMonad.__bind.
  unfold pointwise_relation in H_eq_g.

  (* Get distributions from fx and fy *)
  destruct (fx.(legal).(Legal_exists)) as [dx Hdx].
  destruct (fy.(legal).(Legal_exists)) as [dy Hdy].
  
  (* Use H_eq_f to show dx and dy are related *)
  assert (dy ∈ fx.(distr)) as Hdy_fx. {
    apply H_eq_f.
    exact Hdy.
  }

  (* For each a in dx.(pset), get distributions from gx and gy *)
  assert (exists lx, 
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (gx a).(distr)) dx.(pset) lx) as [lxx Hlxx]. {
    apply forall_exists_Forall2_exists.
    intros a.
    destruct ((gx a).(legal).(Legal_exists)) as [d Hd].
    exists (dx.(prob) a, d).
    split; [reflexivity | exact Hd].
  }

  assert (exists lx,
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (gy a).(distr)) dx.(pset) lx) as [lxy Hlxy]. {
    apply forall_exists_Forall2_exists.
    intros a.
    destruct ((gy a).(legal).(Legal_exists)) as [d Hd].
    exists (dx.(prob) a, d).
    split; [reflexivity | exact Hd].
  }

  assert (exists ly,
    Forall2 (fun a '(r, d) => r = dy.(prob) a /\ d ∈ (gy a).(distr)) dy.(pset) ly) as [lyy Hlyy]. {
    apply forall_exists_Forall2_exists.
    intros a.
    destruct ((gy a).(legal).(Legal_exists)) as [d Hd].
    exists (dy.(prob) a, d).
    split; [reflexivity | exact Hd].
  }

  (* Now we can construct dsx and dsy using Forall2_imply_event_sum_distr_imply_event *)
  assert (exists dxx dxy dyy,
    ProbDistr.sum_distr lxx dxx /\ 
    ProbDistr.sum_distr lxy dxy /\ 
    ProbDistr.sum_distr lyy dyy /\
    ProbDistr.imply_event dxx dxy /\
    ProbDistr.equiv dxy dyy) as [dxx [dxy [dyy [Hsum_xx [Hsum_xy [Hsum_yy [Himply Hequiv]]]]]]].
  {
    (* First, get the summed distributions using ProbDistr_sum_distr_exists *)
    destruct (ProbDistr_sum_distr_exists lxx) as [dxx Hsum_xx].
    destruct (ProbDistr_sum_distr_exists lxy) as [dxy Hsum_xy].
    destruct (ProbDistr_sum_distr_exists lyy) as [dyy Hsum_yy].
    exists dxx, dxy, dyy.
    split.
    + exact Hsum_xx.
    + split.
      * exact Hsum_xy.
      * split.
        - exact Hsum_yy.
        - split.
          ++ apply Forall2_imply_event_sum_distr_imply_event with lxx lxy.
            +++ apply (Forall2_pointwise_mono_aux A dx gx gy lxx lxy).
              -- exact H_eq_g.
              -- exact Hlxx.
              -- exact Hlxy.
            +++ exact Hsum_xx.
            +++ exact Hsum_xy.
          ++ apply (bind_congr_aux dx dy fx gy lxy lyy dxy dyy); assumption.
  }

  exists dxx, dyy.
  split; [| split].
  - (* Show dxx belongs to bind fx gx *)
    exists dx, lxx.
    split; [exact Hdx | split; [exact Hlxx | exact Hsum_xx]].

  - (* Show dyy belongs to bind fy gy *)
    exists dy, lyy.
    split; [exact Hdy | split; [exact Hlyy | exact Hsum_yy]].

  - (* Use transitivity of imply_event through dxy *)
    apply ProbDistr_imply_event_trans with dxy.
    + exact Himply.
    + apply ProbDistr_imply_event_refl_setoid.
      apply ProbDistr_equiv_equiv_event.
      exact Hequiv.
Qed.


#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Proof.
  unfold Proper, respectful.
  intros fx fy H_eq_f gx gy H_eq_g.
  unfold ProbMonad.equiv_event in *.
  assert (pointwise_relation A ProbMonad.imply_event gx gy) as H_le_g.
  {
    unfold pointwise_relation in *.
    unfold ProbMonad.imply_event.
    intros.
    specialize (H_eq_g a).
    destruct H_eq_g as [d1 [d2 [Hd1 [Hd2 H_eq_g]]]].
    exists d1, d2.
    repeat split; [tauto | tauto |].
    specialize(ProbDistr_biliteral_imply_event_iif_equiv_event d1 d2) as H.
    destruct H as [_ H].
    apply H in H_eq_g.
    tauto.
  }
  assert (pointwise_relation A ProbMonad.imply_event gy gx) as H_ge_g.
  {
    unfold pointwise_relation in *.
    unfold ProbMonad.imply_event.
    intros.
    specialize (H_eq_g a).
    destruct H_eq_g as [d1 [d2 [Hd1 [Hd2 H_eq_g]]]].
    exists d2, d1.
    repeat split; [tauto | tauto |].
    specialize(ProbDistr_biliteral_imply_event_iif_equiv_event d1 d2) as H.
    destruct H as [_ H].
    apply H in H_eq_g.
    tauto.
  }
  specialize (ProbMonad_bind_mono_event A fx fy H_eq_f gx gy H_le_g) as H_le.
  symmetry in H_eq_f.
  specialize (ProbMonad_bind_mono_event A fy fx H_eq_f gy gx H_ge_g) as H_ge.

  clear H_le_g H_ge_g H_eq_g H_eq_f.

  unfold ProbMonad.imply_event in *.

  pose proof (x  <- fx;; gx x).(legal).(Legal_exists) as [d1 Hd1].
  pose proof (y  <- fy;; gy y).(legal).(Legal_exists) as [d2 Hd2].
  exists d1.
  exists d2.
  split; [exact Hd1 | split; [exact Hd2 |]].
  apply ProbDistr_biliteral_imply_event_iif_equiv_event.

  assert (ProbDistr.imply_event d1 d2) as H_imply_ge. {
    destruct H_le as [d1' [d2' [Hd1' [Hd2' H_le']]]].
    pose proof ((x  <- fx;; gx x).(legal).(Legal_unique) d1 d1' Hd1 Hd1') as Hx.
    apply ProbDistr_equiv_equiv_event in Hx.
    rewrite Hx.
    pose proof ((y  <- fy;; gy y).(legal).(Legal_unique) d2 d2' Hd2 Hd2') as Hy.
    apply ProbDistr_equiv_equiv_event in Hy.
    rewrite Hy.
    tauto.
  }

  assert (ProbDistr.imply_event d2 d1) as H_imply_le. {
    destruct H_ge as [d2' [d1' [Hd2' [Hd1' H_le']]]].
    pose proof ((x  <- fx;; gx x).(legal).(Legal_unique) d1 d1' Hd1 Hd1') as Hx.
    apply ProbDistr_equiv_equiv_event in Hx.
    rewrite Hx.
    pose proof ((y  <- fy;; gy y).(legal).(Legal_unique) d2 d2' Hd2 Hd2') as Hy.
    apply ProbDistr_equiv_equiv_event in Hy.
    rewrite Hy.
    tauto.
  }

  split; [exact H_imply_ge | exact H_imply_le].
Qed.
(* Admitted. * Level 2 *)

(*
  Name: is_det_compute_pr_01:
  Property: Auxiliary Theorem
  Description:
    for any d s.t. is_det P d,
      compute_pr d is 0 if P is false
                   is 1 if P is true
*)
Theorem is_det_compute_pr_01:
  forall P d,
    ProbDistr.is_det P d ->
    ((~P -> ProbDistr.compute_pr d 0%R) /\
    (P-> ProbDistr.compute_pr d 1%R)).
Proof.
  intros.
  unfold ProbDistr.is_det in H.
  destruct H as [Ha [Hb Hc]].
  unfold ProbDistr.compute_pr.
  split.
  - intros.
    exists [].
    split.
    + constructor.
    + split.
      * intro Q.
        destruct (eq_dec P Q) as [eq | neq].
        -- subst.
           split.
           ++ simpl; tauto.
           ++ intros.
              destruct H0 as [H0l H0r].
              tauto.
        -- split.
           ++ simpl; tauto.
           ++ intros.
              destruct H0 as [H0l H0r].
              rewrite Ha in H0l.
              simpl in H0l.
              tauto.
      * unfold sum_prob.
        simpl.
        reflexivity.
  - intros.
    exists [P].
    split.
    + constructor; [simpl; tauto | constructor].
    + split.
      * intro Q.
        destruct (eq_dec P Q) as [eq | neq].
        -- subst.
           split; rewrite Ha; [tauto | tauto].
        -- split; rewrite Ha; [simpl; tauto | tauto].
      * unfold sum_prob.
        simpl.
        rewrite Hb.
        lra.
Qed.

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
  specialize (ProbMonad.__ret_Legal y) as H_legal_y'.
  apply H_legal_y' in H1 as H_legal_y.
  unfold ProbMonad.__ret in *.
  
  specialize (is_det_compute_pr_01) as H_01.
  specialize (H_01 x d1 H0) as H_01_x.
  specialize (H_01 y d2 H1) as H_01_y.
  
  destruct (classic x) as [Hx | Hnx].
  - exists 1%R, 1%R.

    destruct H_01_x as [_ H_01_x].
    apply H_01_x in Hx as H_x_prob.
    destruct H_01_y as [_ H_01_y].
    apply H in Hx as Hy.
    apply H_01_y in Hy as H_y_prob.
    repeat split; [exact H_x_prob | exact H_y_prob | lra].
  - specialize (ProbDistr_compute_pr_exists d2) as [r2 ?].
    exists 0%R, r2.
    destruct H_01_x as [H_01_x _].
    apply H_01_x in Hnx as H_x_prob.
    repeat split; [exact H_x_prob | exact H2 |].
    pose proof (ProbDistr_compute_pr_nonneg d2 r2 H_legal_y H2).
    lra.
Qed.
(* Admitted. * Level 2 *)

#[export] Instance ProbMonad_ret_congr_event:
  Proper (iff ==> ProbMonad.equiv_event) ret.
Proof.
  unfold Proper, respectful.
  intros.
  unfold ProbMonad.equiv_event.
  specialize ((ret x).(legal).(Legal_exists)) as [d1 H1].
  specialize ((ret y).(legal).(Legal_exists)) as [d2 H2].
  exists d1, d2.
  split; [tauto | ].
  split; [tauto | ].
  specialize (ProbMonad_ret_mono_event x y) as H_le'.
  specialize (ProbMonad_ret_mono_event y x) as H_ge'.
  unfold Basics.impl in *.
  destruct H as [H_if H_rev_if].
  apply H_le' in H_if as H_le.
  apply H_ge' in H_rev_if as H_ge.
  clear H_le' H_ge'.
  unfold ProbMonad.imply_event in *.
  destruct H_le as [d1' [d2' [H_le1 [H_le2 H_le3]]]].
  destruct H_ge as [d2'' [d1'' [H_ge2 [H_ge1 H_ge3]]]].
  pose proof ((ret x).(legal).(Legal_unique) d1 d1' H1 H_le1) as H_unique1'.
  pose proof ((ret x).(legal).(Legal_unique) d1' d1'' H_le1 H_ge1) as H_unique1''.
  pose proof ((ret y).(legal).(Legal_unique) d2 d2' H2 H_le2) as H_unique2'.
  pose proof ((ret y).(legal).(Legal_unique) d2' d2'' H_le2 H_ge2) as H_unique2''.
  pose proof (ProbDistr_compute_pr_exists d1) as [r1 Hr1].
  pose proof (ProbDistr_compute_pr_exists d2) as [r2 Hr2].

  apply ProbDistr_equiv_equiv_event in H_unique1'.
  apply ProbDistr_equiv_equiv_event in H_unique1''.
  apply ProbDistr_equiv_equiv_event in H_unique2'.
  apply ProbDistr_equiv_equiv_event in H_unique2''.
  assert (ProbDistr.imply_event d1 d2) as H_le_final. {
    rewrite H_unique1'.
    rewrite H_unique2'.
    exact H_le3.
  }
  assert (ProbDistr.imply_event d2 d1) as H_ge_final. {
    rewrite H_unique1'.
    rewrite H_unique1''.
    rewrite H_unique2'.
    rewrite H_unique2''.
    exact H_ge3.
  }
  apply ProbDistr_biliteral_imply_event_iif_equiv_event.
  split; [exact H_le_final | exact H_ge_final].
Qed.

(* Admitted. * Level 2 *)

(**
Auxiliary Lemma :
  construt a list of distribution that satisfies congruence with distribution
*)
Lemma bind_distr_exists:
  forall (A B C: Type) 
        (dstr_a: Distr A) 
        (g: A -> ProbMonad.M B)
        (h: B -> ProbMonad.M C),
  exists lac: list (R * Distr C),
        Forall2 (fun a '(r, d) => r = dstr_a.(prob) a /\ exists ga: Distr B, (g a).(distr) ga /\
                  exists l_sum_to_bc: list (R * Distr C),
                    (Forall2 (fun b '(r, d) => 
                                r = ga.(prob) b /\ d ∈ (h b).(distr)) 
                      ga.(pset) l_sum_to_bc) /\
                      ProbDistr.sum_distr l_sum_to_bc d)
        dstr_a.(pset) lac.
Admitted.

(**
Auxiliary Lemma:
 
construct a satisfied distr and prove its bind satisfies the equivlance with prob
*)
Lemma in_pset_equiv_with_prob:
  forall (A B C: Type)
         (dstr_c: Distr C)
         (lst_ac: list (R * Distr C))
         (dstr_a: Distr A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  Forall2 (fun a '(r, d) => r = dstr_a.(prob) a /\ 
        exists ga: Distr B, (g a).(distr) ga /\ 
        exists l_sum_to_bc: list (R * Distr C),
        (Forall2 (fun b '(r, d) => r = ga.(prob) b /\ d ∈ (h b).(distr)) ga.(pset) l_sum_to_bc) /\ ProbDistr.sum_distr l_sum_to_bc d) dstr_a.(pset) lst_ac ->
  (forall a: C,
     In a dstr_c.(pset) <-> In a (concat (map (fun '(_, d) => d.(pset)) lst_ac))) /\
  (forall a: C,
     dstr_c.(prob) a = sum (map (fun '(r, d) => (r * d.(prob) a)%R) lst_ac)).
Admitted.

(** 
Auxliary Lemma:
  bind congruence with distribution
*)
Lemma bind_congr_distr_aux:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C)
         (dstr_c: Distr C)
         (dstr_a: Distr A)
         (lst_ac: list (R * Distr C))
         (dstr_b: Distr B)
         (lbc: list (R * Distr C)),
  dstr_a ∈ f.(distr) ->
  Forall2 (fun a '(r, d) =>
             r = dstr_a.(prob) a /\
             d ∈ (bind (g a) h).(distr))
          dstr_a.(pset) lst_ac ->
  ProbDistr.sum_distr lst_ac dstr_c ->
  dstr_b ∈ (ProbMonad.bind f g).(distr) ->
  Forall2 (fun b '(r, d) =>
             r = dstr_b.(prob) b /\
             d ∈ (h b).(distr))
          dstr_b.(pset) lbc ->
  ProbDistr.sum_distr lbc dstr_c.
Admitted.

(*
  Name: forall2_H
  Property: Auxiliary Theorem
  Description:
    Forall2 P l1 l2 -> (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2
*)
Lemma forall2_H:
  forall {A B: Type} (l1: list A) (l2: list B) (P Q: A -> B -> Prop) ,
    Forall2 P l1 l2 ->
    (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 Q l1 l2.
Proof.
  intros.
  induction H.
  - constructor.
  - constructor; auto.
  + apply H0; auto.
  ++ left; auto.
  ++ left; auto.
  + apply IHForall2.
    intros.
    apply H0; auto.
    right; auto.
    right; auto.
Qed.

(*
  Name: bind_congr
  Property: Auxiliary Theorem
  Description:
    If two distributions are equivalent and mapped by the same function g,
    then their bind results are also equivalent.
*)
Lemma bind_congr:
  forall (A B: Type)(c: ProbMonad.M A)(f1 f2: A -> ProbMonad.M B),
    (forall a, f1 a == f2 a) ->
    forall d, d ∈ (bind c f1).(distr) -> d ∈ (bind c f2).(distr).
Proof.
  intros.
  unfold bind in *; simpl in *.
  unfold ProbMonad.__bind in *; simpl in *.
  unfold ProbMonad.equiv in *; sets_unfold.
  destruct H0 as [d' [l [Hd' [Hl Hsum_distr]]]].
  exists d', l.
  split; auto. split; auto.
  eapply forall2_H; eauto.
  intros.
  destruct b.
  split.
  - tauto.
  - destruct H2.
    apply H; auto.
Qed.

Lemma bind_assoc:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Proof.
  intros.
  unfold ProbMonad.equiv.
  sets_unfold.
  intros dstr_c.
  split.
  + intros.
    destruct H as [dstr_b [lst_c [[dstr_a [lst_b [H_dstr_a [H_forall2_atob H_sum_distr_b]]]] [H_forall2_btoc H_sum_distr_c]]]].
    pose proof bind_distr_exists _ _ _ dstr_a g h as H_distr_exists.
    destruct H_distr_exists as [lst_ac H_forall2_atoc].
    exists dstr_a, lst_ac.
    split.
    2: split.
    - auto.
    - pose proof Forall2_imply_congr dstr_a.(pset) lst_ac as H_forall2_imply.
      eapply H_forall2_imply.
      * apply H_forall2_atoc.
      * intros a [r d].
        intros H_in_dstr_a H_in_lst_ac [H_eq H_exists].
        destruct H_exists as [ga [Hga [l_sum_to_bc [H_forall2_bc H_sum_bc]]]].
        split; auto.
        sets_unfold.
        exists ga, l_sum_to_bc.
        split; auto.
    - destruct H_sum_distr_c as [H_sum_lbdc _].
      destruct H_sum_distr_b as [H_sum_ladb _]. 
      pose proof in_pset_equiv_with_prob _ _ _ dstr_c lst_ac dstr_a g h H_forall2_atoc as [H_pset_equiv H_prob_equiv].
      split.
      ++ apply H_sum_lbdc.
      ++ apply H_pset_equiv.
      ++ exact H_prob_equiv.
  + intros H.
    destruct H as [dstr_a [lst_ac [H_distr_a [Hlac H_sum_distr_ladc]]]].
    pose proof (ProbMonad.bind f g).(legal).(Legal_exists) as [dstr_b Hdb].
    assert (
      exists lbc: list (R * Distr C),
        Forall2 (fun b '(r, d) => 
                  r = dstr_b.(prob) b /\ 
                  (h b).(distr) d)
        dstr_b.(pset) lbc
    ). {
      induction dstr_b.(pset) as [|b l].
      - exists nil.
        repeat constructor.
      - destruct IHl as [lbc Hlbc].
        pose proof (h b).(legal).(Legal_exists) as [hb Hhb].
        exists ((dstr_b.(prob) b, hb) :: lbc).
        constructor.
        * sets_unfold in Hhb.
          split; auto.
        * apply Hlbc.
    }
    destruct H as [lbc Hlbc].
    exists dstr_b, lbc.
    split.
    2:auto.
    - apply Hdb.
    - split.
      apply Hlbc.
      pose proof bind_congr_distr_aux _ _ _ f g h dstr_c dstr_a lst_ac dstr_b lbc H_distr_a Hlac H_sum_distr_ladc Hdb Hlbc.
      apply H.
Qed.
(**Admitted.  Level 3 *)

Lemma bind_assoc_event:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M Prop),
  ProbMonad.equiv_event
    (bind (bind f g) h)
    (bind f (fun a => bind (g a) h)).
Proof.
  intros.
  unfold ProbMonad.equiv_event.
  pose proof bind_assoc _ _ _ f g h as H_bind_assoc.
  unfold ProbMonad.equiv in H_bind_assoc.
  sets_unfold in H_bind_assoc.
  pose proof (bind (bind f g) h).(legal).(Legal_exists) as [d Hd].
  exists d, d.
  repeat split.
  - apply Hd.
  - specialize (H_bind_assoc d).
    destruct H_bind_assoc as [? _].
    apply H in Hd.
    apply Hd.
  - reflexivity.
Qed.
(** Admitted.  Level 3 *)


(*
  Name: Forall2_singleton_inv
  Property: Auxiliary Theorem
  
  Forall2 rel [a] l -> exists b, l = [b] /\ rel a b

  used to extract the only element in a list under singleton mapping.
*)
Lemma Forall2_singleton_inv : forall A B (rel : A -> B -> Prop) (a : A) (l : list B),
  Forall2 rel [a] l -> exists b, l = [b] /\ rel a b.
Proof.
  intros A B rel a l H.
  inversion H; subst; simpl.
  exists y.
  assert (l' = []). {
    inversion H4.
    reflexivity.
  }
  subst.
  split.
  - reflexivity.
  - tauto.
Qed.


(*
  Name: sum_distr_singleton_preserve:
  Property: Auxiliary Theorem
  Description:
    ProbDistr.sum_distr [(1, d)] ds -> d == ds as long as d is legal
*)
Lemma sum_distr_singleton_preserve:
  forall {A: Type} (r : R) (d: Distr A) (ds : Distr A),
    r = 1%R ->
    ProbDistr.legal d ->
    ProbDistr.sum_distr [(r, d)] ds 
    -> ProbDistr.equiv d ds.
Proof.
  intros.
  destruct H1 as [H1 ? ? ].
  simpl in *.
  rewrite app_nil_r in sum_pset_valid.
  unfold ProbDistr.equiv.
  split.
  + intros.
    specialize (sum_prob_valid a) as H_prob.
    rewrite H_prob.
    nra.
  + destruct H0 as [H0 _ _ _].
    symmetry in sum_pset_valid.
    apply NoDup_Permutation; [exact H0 | exact H1 | exact sum_pset_valid].
Qed.

(*
  Name:bind_equiv_congr
  Property: Auxiliary Theorem
  Description:
    If two functions are equivalent, then their bind results are also equivalent.
*)

Lemma bind_equiv_congr:
  forall (A B: Type) (c: ProbMonad.M A) (f1 f2: A -> ProbMonad.M B),
    (forall a, f1 a == f2 a) ->
    bind c f1 == bind c f2.
Proof.
  intros.
  unfold ProbMonad.equiv; sets_unfold.
  intros.
  split.
  - apply bind_congr; auto.
  - apply bind_congr.
    intros.
    symmetry.
    apply H.
Qed.

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> ProbMonad.M B),
  bind (ret a) f == f a.
Proof.
  intros.
  unfold bind, ret; simpl.
  remember (ProbMonad.bind (ProbMonad.ret a) f) as lhs.
  unfold ProbMonad.bind in *.
  unfold ProbMonad.equiv in *; sets_unfold.
  intro ds.
  split.
  + intro; unfold ProbMonad.__bind in *; subst.
    destruct H.
    destruct H as [l [Hret [Hl Hsum_distr]]].
    destruct Hret as [Hret1 [Hret2 Hret3]].
    rewrite Hret1 in Hl.
    apply Forall2_singleton_inv in Hl as [[r ds'] [Hrds' [Hr Hds']]]. (* extract distr intermediate *)
    rewrite Hret2 in Hr; subst r.
    subst l.
    pose proof ((f a).(legal).(Legal_legal) ds' Hds') as Hds'_legal.
    pose proof (sum_distr_singleton_preserve 1%R ds' ds eq_refl Hds'_legal Hsum_distr) as H_equiv.
    pose proof ((f a).(legal).(Legal_congr) ds' ds H_equiv Hds') as H_congr.
    exact H_congr.
  + intro. (* 
  idea: 
  先用 exists 搞一个 lhs.(distr) 的 ds' 出来，证明 ds' ∈ (f a).(distr) 
  [通过 sum_distr_singleton_preserve 证明, 中间变量是 ds'' ∈ (f a).(distr) => ds'' == ds' => ds' ∈ (f a).(distr) by Legal_congr].

  然后 (f a) Legal_unique 得到 ds'==ds, 再 lhs Legal_congr, 得到 ds ∈ lhs.(distr)
  *)
    pose proof (lhs.(legal).(Legal_exists)) as [ds' Hds'].
    assert (ds' ∈ lhs.(distr)) as Hds'_copy. {
      exact Hds'.
    }
    rewrite Heqlhs in Hds'.
    destruct Hds' as [x [l [Hret [Hl Hsum_distr]]]].
    destruct Hret as [Hret1 [Hret2 Hret3]].
    rewrite Hret1 in Hl.
    apply Forall2_singleton_inv in Hl as [[r ds''] [Hrds'' [Hr Hds'']]]. (* extract distr intermediate *)
    subst l.
    rewrite Hret2 in Hr; subst r.
    pose proof ((f a).(legal).(Legal_legal) ds'' Hds'') as Hds''_legal.
    pose proof (sum_distr_singleton_preserve 1%R ds'' ds' eq_refl Hds''_legal Hsum_distr) as H_equiv.
    pose proof ((f a).(legal).(Legal_congr) ds'' ds' H_equiv Hds'') as H_congr.
    pose proof ((f a).(legal).(Legal_unique) ds' ds H_congr H)as H_equiv2.
    pose proof(lhs.(legal).(Legal_congr) ds' ds H_equiv2 Hds'_copy) as H_congr2.
    exact H_congr2.
Qed.
(* Admitted. * Level 3 *)

(*
  Name: ProbMonad_equiv_equiv_event
  Property: Auxiliary Theorem
  Description:
    ProbMonad.equiv f1 f2 -> ProbMonad.equiv_event f1 f2
*)
Theorem ProbMonad_equiv_equiv_event:
  forall (f1 f2: ProbMonad.M Prop),
    ProbMonad.equiv f1 f2 ->
    ProbMonad.equiv_event f1 f2.
Proof.
  intros.
  unfold ProbMonad.equiv_event.
  unfold ProbMonad.equiv in H. sets_unfold in H.
  pose proof (f1.(legal).(Legal_exists)) as [d1 Hd1].
  apply H in Hd1 as Hd2.
  exists d1, d1.
  split; [exact Hd1 | split; [exact Hd2 | reflexivity]].
Qed.


Lemma bind_ret_l_event:
  forall (A: Type)
         (a: A)
         (f: A -> ProbMonad.M Prop),
  ProbMonad.equiv_event (bind (ret a) f) (f a).
Proof.
  intros.
  specialize (bind_ret_l A Prop a f) as H.
  apply ProbMonad_equiv_equiv_event in H.
  tauto.
Qed.
(* Admitted. * Level 3 *)

Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
Proof.
  intros.
  unfold Always.
  unfold Hoare.
  sets_unfold.
  split.
  + intros.
    specialize (H0 a).
    unfold ProbMonad.compute_pr in *.
    destruct H1 as [d1 [Hd1]].
    sets_unfold in Hd1.
    apply H0.
    exists d1.
    split.
    2:{ exact H1. }
    - clear H1.
    assert (c2 = fun b => ret (f b)) as Hc. {
      extensionality b.
      apply H.
    }
    subst c2.
    clear H0 H.
    remember (ProbMonad.bind (ProbMonad.bind c1 (fun a : A => ProbMonad.ret (f a))) (fun res : B => ProbMonad.ret (P res))) as b1.
    remember (ProbMonad.bind c1 (fun res: A => ProbMonad.ret (P (f res)))) as b2.
    assert (d1 ∈ b1.(distr)) as Hd1'.
    { 
      subst b2.
      subst b1.
      sets_unfold.
      unfold bind, ret in *. simpl in *.
      tauto.
    }
    clear Hd1.
    remember (res <- c1 ;; ret (P (f res))) as t2.
    assert (b2 = t2) as Hb2. {
      subst b2.
      subst t2.
      unfold bind, ret in *.
      simpl in *.
      tauto.
    }
    rewrite <- Hb2.
    clear Hb2 Heqt2 t2.
    remember (ProbMonad.bind c1 (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res)))) as b3. 
    assert(b1 == b3) as Hb1. {
      subst b3.
      subst b1.
      apply bind_assoc.
    }
    assert (d1 ∈ b3.(distr)) as Hd1''. {
      unfold ProbMonad.equiv in Hb1.
      apply Hb1 in Hd1'.
      exact Hd1'.
    }
    remember (fun res: A => ProbMonad.ret (P (f res))) as f1.
    clear Hb1 Hd1'.
    remember (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res))) as f2.
    assert (forall x, f1 x == f2 x) as Hf. {
      subst f1.
      subst f2.
      intros.
      pose proof bind_ret_l _ _ (f x) (fun res : B => ProbMonad.ret (P res)).
      rewrite H.
      reflexivity.
    }
    specialize (bind_equiv_congr _ _ c1 f1 f2 Hf) as H_congr.
    assert (b2 == b3) as Hd1'''. {
      subst b2.
      subst b3.
      apply H_congr.
    }
    clear H_congr Hf.
    apply Hd1'''.
    exact Hd1''.
  + intros.
  specialize (H0 a).
  unfold ProbMonad.compute_pr in *.
  destruct H1 as [d1 [Hd1]].
  sets_unfold in Hd1.
  apply H0.
  exists d1.
  split.
  2:{ exact H1. }
  - clear H1.
  assert (c2 = fun b => ret (f b)) as Hc. {
    extensionality b.
    apply H.
  }
  subst c2.
  clear H0 H.
  remember (ProbMonad.bind (ProbMonad.bind c1 (fun a : A => ProbMonad.ret (f a))) (fun res : B => ProbMonad.ret (P res))) as b1.
  remember (ProbMonad.bind c1 (fun res: A => ProbMonad.ret (P (f res)))) as b2.
  assert (d1 ∈ b2.(distr)) as Hd1'.
  { 
    subst b2.
    subst b1.
    sets_unfold.
    unfold bind, ret in *. simpl in *.
    tauto.
  }
  clear Hd1.
  remember (res <- c1 ;; ret (P (f res))) as t2.
  assert (b2 = t2) as Hb2. {
    subst b2.
    subst t2.
    unfold bind, ret in *.
    simpl in *.
    tauto.
  }
  assert (d1 ∈ t2.(distr)) as Hd1''. {
    subst t2.
    rewrite <- Hb2.
    exact Hd1'.
  }
  clear Hb2 Hd1'.
  remember (res <- (a0 <- c1;; ret (f a0));; ret (P res)) as t3.
  assert (b1 == t3) as Hb2. {
    subst b1.
    subst t3.
    unfold bind, ret in *.
    simpl in *.
    reflexivity.
  }
  apply Hb2.
  remember (ProbMonad.bind c1 (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res)))).
  assert (b1 == m) as Hm. {
    subst m.
    subst b1.
    apply bind_assoc.
  }
  apply Hm.
  remember (fun res: A => ProbMonad.ret (P (f res))) as f1.
  remember (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res))) as f2.
  assert (forall x, f1 x == f2 x) as Hf. {
    subst f1.
    subst f2.
    intros.
    pose proof bind_ret_l _ _ (f x) (fun res : B => ProbMonad.ret (P res)).
    rewrite H.
    reflexivity.
  }
  specialize (bind_equiv_congr _ _ c1 f1 f2 Hf) as H_congr.
  assert (b2 == m) as Hd1'''. {
    subst b2.
    subst m.
    apply H_congr.
  }
  clear H_congr Hf.
  apply Hm.
  assert (t2 == b2) as Hb3. {
    subst t2.
    subst b2.
    unfold bind, ret in *.
    simpl in *.
    subst f1.
    reflexivity.
  }
  assert (d1 ∈ b2.(distr)) as Hd1'''''. {
    apply Hb3.
    exact Hd1''.
  }
  apply Hm.
  apply Hd1'''.
  exact Hd1'''''.
Qed.    


(* 
  Property: Auxiliary Theorem
  Description:
    if ProbDistr.is_det a d, then:
      d.(prob) b = {
        1, if a = b
        0, if a ≠ b
      }
*)
Theorem is_det_prob_01:
  forall {A : Type} (d : Distr A) (a: A) (b: A),
    ProbDistr.is_det a d ->
    ((a = b -> d.(prob) b = 1%R) /\ (a <> b -> d.(prob) b = 0%R)).
Proof.
  intros.
  split; intro.
  - subst.
    unfold ProbDistr.is_det in H.
    destruct H as [H1 [H2 H3]].
    exact H2.
  - unfold ProbDistr.is_det in H.
    destruct H as [H1 [H2 H3]].
    specialize (H3 b H0).
    exact H3.
Qed. 

(* 
  direct auxiliary theorem for sum_distr_is_det_list_exists 
  // reused by sum_distr_is_det_preserve 

  pset is preserved for sum_distr_is_det, or namely,
   d0.(pset) = concat (map (fun '(_, d) => d.(pset)) ds_list)
*)
Theorem sum_distr_is_det_list_exists_aux0:
  forall {A: Type} (d0 : Distr A) (ds_list : list(R * Distr A)),
    Forall2 (fun a '(r, d) => r = d0.(prob) a /\ ProbDistr.is_det a d) d0.(pset) ds_list ->
    concat (map (fun '(_, d) => d.(pset)) ds_list) = d0.(pset).
Proof. 
  intros ? ? ? Hds_list.
  revert Hds_list.
  revert ds_list.
  induction d0.(pset).
  + intros ds_list Hds_list.
    inversion Hds_list.
    simpl.
    reflexivity.
  + intros ds_list Hds_list_app.
    inversion Hds_list_app.
    subst l0 a.
    subst ds_list.
    specialize (IHl l' H3).
    clear Hds_list_app H3.
    simpl.
    rewrite IHl.
    unfold ProbDistr.is_det in H1.
    destruct y.
    destruct H1 as [_ [Hpset_eq_x _]].
    rewrite Hpset_eq_x.
    simpl.
    reflexivity.
Qed.


(* 
  direct auxiliary theorem for sum_distr_is_det_list_exists
  convert original Forall2 to direct computable prob form 
*)
Theorem sum_distr_is_det_list_exists_aux1:
  forall {A: Type} (d0 : Distr A) (lpset: list A) (ldistr: list (R * Distr A)),
  Forall2 (fun a '(r, d) => r = d0.(prob) a /\ ProbDistr.is_det a d) lpset ldistr -> 
  (forall (a0: A),
    Forall2 
      (fun a '(r, d) => 
        (a = a0 ->  r * (d.(prob) a0) = d0.(prob) a0)%R /\ 
        (a <> a0 -> r * (d.(prob) a0) = 0)%R
      ) 
      lpset ldistr).
Proof.
  intros ? ? ? ? H_Forall2 ?.
  induction H_Forall2 as [| x y l1tail l2tail Hrel Htail].
  + constructor.
  (* l1 = x::l1tail, l2 = y::l2tail *)
  + constructor; [|exact IHHtail].
    destruct y. (* into (r, d) *)
    destruct Hrel as [H_r H_d].
    split; intro H.
    (* x=a0 *)
    - specialize(is_det_prob_01 d x a0 H_d) as [H_prob1 _].
      specialize(H_prob1 H).
      subst x.
      rewrite H_prob1.
      rewrite H_r.
      nra.
    (* x<>a0*)
    - specialize(is_det_prob_01 d x a0 H_d) as [_ H_prob0].
      specialize(H_prob0 H).
      rewrite H_prob0.
      rewrite H_r.
      nra.
Qed.


(* 
  direct auxiliary theorem for sum_distr_is_det_list_exists
  if not in lpset, sum prob = 0 
*)
Theorem sum_distr_is_det_list_exists_aux2:
  forall {A: Type} (d0 : Distr A) (lpset: list A) (ldistr: list (R * Distr A)) (a0: A),
  (Forall2 
      (fun a '(r, d) => 
        (a = a0 ->  r * (d.(prob) a0) = d0.(prob) a0)%R /\ 
        (a <> a0 -> r * (d.(prob) a0) = 0)%R
      ) 
      lpset ldistr)
  -> ~In a0 lpset
  -> sum (map (fun '(r, d) => (r * d.(prob) a0)%R) ldistr) = 0%R.
Proof.
  intros ? ? ? ? ? H H_not_in.
  induction H as [|x y l1tail l2tail Hhead Htail].
  - simpl; reflexivity.
  - destruct y as [r d].
    assert (~In a0 l1tail) as H_not_in_tail. {
      intro H_in_tail.
      apply H_not_in.
      right.
      exact H_in_tail.
    }
    specialize(IHHtail H_not_in_tail) as H_tail_sum.
    simpl.
    rewrite H_tail_sum.
    assert (x <> a0) as H_neq. {
      intro H_eq.
      apply H_not_in.
      left.
      exact H_eq.
    }
    destruct Hhead as [_ Hhead].
    specialize (Hhead H_neq).
    nra.
Qed.

(* 
  direct auxiliary theorem for sum_distr_is_det_list_exists 
  if in lpset and lpset nodup, sum prob a = d0.prob a
*)
Theorem sum_distr_is_det_list_exists_aux3:
  forall {A: Type} (d0 : Distr A) (lpset: list A) (ldistr: list (R * Distr A)) (a0: A),
  (Forall2 
      (fun a '(r, d) => 
        (a = a0 ->  r * (d.(prob) a0) = d0.(prob) a0)%R /\ 
        (a <> a0 -> r * (d.(prob) a0) = 0)%R
      ) 
      lpset ldistr)
  -> In a0 lpset
  -> NoDup lpset
  -> sum (map (fun '(r, d) => (r * d.(prob) a0)%R) ldistr) = d0.(prob) a0.
Proof.
  intros ? ? ? ? ? H_Forall2 H_in H_no_dup.
  induction H_Forall2 as [| x y l1tail l2tail Hhead Htail].
  - inversion H_in.
  - destruct (classic (x = a0)) as [H_ishead| H_nhead]. (* whether a0 is the head *)
    + subst a0.
      destruct y as [r d].
      destruct Hhead as [Hhead _].
      specialize (Hhead eq_refl) as H_head_prob.
      assert (~In x l1tail) as H_not_in_tail. {
        apply NoDup_cons_iff in H_no_dup.
        destruct H_no_dup as [H_no_dup _].
        apply H_no_dup.
      }
      specialize (sum_distr_is_det_list_exists_aux2 d0 l1tail l2tail x Htail H_not_in_tail) as H_tail_prob.
      simpl. (* split sum in objective *)
      rewrite H_tail_prob.
      rewrite H_head_prob.
      nra.
    + assert (In a0 l1tail) as H_in_tail.
      {
        destruct H_in as [H1 | H2].
        - subst a0.
          contradiction.
        - exact H2.
      }
      assert (NoDup l1tail) as H_no_dup_tail. {
        apply NoDup_cons_iff in H_no_dup.
        destruct H_no_dup as [_ H_no_dup].
        exact H_no_dup.
      }
      specialize (IHHtail H_in_tail H_no_dup_tail) as H_tail_prob.
      simpl.
      rewrite H_tail_prob.
      destruct y as [r d].
      destruct Hhead as [_ Hhead].
      specialize (Hhead H_nhead) as H_head_prob.
      nra.
Qed.

(*   
  direct auxiliary theorem for sum_distr_is_det_list_exists 
  // reused by sum_distr_is_det_preserve 
  sum prob a = d0.prob a 
*)
Theorem sum_distr_is_det_list_exists_aux4:
  forall {A: Type} (d0 : Distr A) (ds_list : list(R * Distr A)),
  ProbDistr.legal d0 ->
  Forall2 (fun a '(r, d) => r = d0.(prob) a /\ ProbDistr.is_det a d) d0.(pset) ds_list ->
  forall a, d0.(prob) a = sum (map (fun '(r, d) => r * d.(prob) a)%R ds_list).
Proof.
  intros ? ? ? H_legal Hds_list a0.
  specialize (sum_distr_is_det_list_exists_aux1 d0 d0.(pset) ds_list Hds_list a0) as H_ds_list_prob_a0.
  destruct (classic (In a0 d0.(pset))) as [H_in | H_nin].
  2 : { (* a0 not in pset*)
    specialize (sum_distr_is_det_list_exists_aux2 d0 d0.(pset) ds_list a0 H_ds_list_prob_a0 H_nin) as H_sum0.
    rewrite H_sum0.
    destruct H_legal as [_ ? ? _].
    specialize (legal_pset_valid a0).
    destruct (classic ((d0.(prob) a0 > 0)%R)) as [H_pos | H_npos].
    - specialize (legal_pset_valid H_pos).
      tauto. (* contradiction *)
    - specialize(legal_nonneg a0).
      nra.
  }
  (* a0 in pset*)
  destruct H_legal as [H_no_dup _ _ _].
  specialize (sum_distr_is_det_list_exists_aux3 d0 d0.(pset) ds_list a0 H_ds_list_prob_a0 H_in H_no_dup) as H_sum_prob.
  symmetry in H_sum_prob.
  exact H_sum_prob.
Qed.


(* 
  direct auxiliary theorem of **bind_ret_r**'s -> direction.
*)
Theorem sum_distr_is_det_list_exists:
  forall {A: Type} (d0 : Distr A),
      ProbDistr.legal d0 ->
      exists ds_list,
        Forall2 (fun a '(r, d) => r = d0.(prob) a /\ ProbDistr.is_det a d) d0.(pset) ds_list /\ ProbDistr.sum_distr ds_list d0.
Proof.
  intros A d0 H_legal.
  remember ((fun (a : A) '(r, d) =>
  r = d0.(prob) a /\ ProbDistr.is_det a d)) as rel.
  assert (forall a : A, exists b : R * Distr A, rel a b) as H_is_det_ex. {
    intros.
    subst.
    specialize (is_det_exists a) as [d Hd].
    exists (d0.(prob) a, d).
    split; [reflexivity | exact Hd]. 
  }
  specialize (forall_exists_Forall2_exists rel d0.(pset) H_is_det_ex) as H_ds_list_ex.
  destruct H_ds_list_ex as [ds_list Hds_list].
  exists ds_list.
  split; [tauto |].
  split; [destruct H_legal ;tauto | |].
  (* pset equal *)
  + intro a.
    subst rel.
    specialize (sum_distr_is_det_list_exists_aux0 d0 ds_list Hds_list) as H_pset_eq.
    rewrite H_pset_eq.
    reflexivity.
  (* prob equal *)
  + subst rel.
    apply sum_distr_is_det_list_exists_aux4; assumption.
Qed.


(*
  direct auxiliary theorem of **bind_ret_r**'s <- direction

  most of the proof can be shared with sum_distr_is_det_list_exists.
*)
Theorem sum_distr_is_det_preserve:
  forall {A: Type} (d0 : Distr A) (ds_list : list (R * Distr A)) (ds : Distr A),
    ProbDistr.legal d0 ->
    Forall2 (fun a '(r, d) => r = d0.(prob) a /\ ProbDistr.is_det a d) d0.(pset) ds_list ->
    ProbDistr.sum_distr ds_list ds ->
    ProbDistr.equiv d0 ds.
Proof.
  intros ? ? ? ? H_legal Hds_list H_sum_distr.
  unfold ProbDistr.equiv.
  split.
  + intro a0.
    destruct H_sum_distr.
    specialize (sum_prob_valid a0) as H_prob_a0.
    rewrite H_prob_a0.
    apply sum_distr_is_det_list_exists_aux4; assumption.
  + destruct H_sum_distr.
    specialize (sum_pset_valid) as H_pset.
    destruct H_legal.
    apply NoDup_Permutation; [exact legal_no_dup | exact sum_pset_no_dup |].
    intro a0.
    specialize (H_pset a0).
    rewrite H_pset.
    clear legal_no_dup legal_nonneg legal_pset_valid legal_prob_1.
    clear sum_pset_no_dup sum_pset_valid sum_prob_valid.
    specialize (sum_distr_is_det_list_exists_aux0 d0 ds_list Hds_list) as H_pset_eq.
    rewrite H_pset_eq.
    reflexivity.
Qed.

Lemma bind_ret_r:
  forall (A: Type)
         (f: ProbMonad.M A),
  bind f ret == f.
Proof.
  intros.
  unfold ProbMonad.equiv; sets_unfold.
  intro ds.
  remember (x <- f;; ret x) as lhs.
  split; intro H; simpl in *; unfold ProbMonad.__bind, ProbMonad.__ret in *.
  + destruct H as [ds' [l [Hds' [Hl Hsum_distr]]]].
    pose proof (f.(legal).(Legal_legal) ds' Hds') as Hds'_legal.
    specialize (sum_distr_is_det_preserve ds' l ds Hds'_legal Hl Hsum_distr) as H_equiv.
    pose proof (f.(legal).(Legal_congr) ds' ds H_equiv Hds') as H_congr.
    exact H_congr.
  + exists ds.
    specialize (f.(legal).(Legal_legal) ds H) as Hds_legal.
    specialize (sum_distr_is_det_list_exists ds Hds_legal) as [ds_list [H_Forall2 H_sum_distr]].
    exists ds_list.
    tauto.
Qed.
(* Admitted. * Level 3 *)

