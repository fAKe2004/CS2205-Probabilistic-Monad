# CS2205-Probabilistic-Monad

Project repo for CS2205 ProbMonad

### level 1 partition

1-4 fAKe (Done)

6-8 Andylinx (Done)

9-11 Zicong Zhang (Done)

12-14 Mikeayaka

```coq
Lemma __bind_legal {A B: Type}:
  forall (f: Distr A -> Prop) (g: A -> Distr B -> Prop),
    Legal f ->
    (forall a, Legal (g a)) ->
    Legal (__bind f g).
Admitted.

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
```

### level 2 partition

15-17 Mikeayaka (Done)

```coq
#[export] Instance ProbMonad_imply_event_refl:
  Reflexive ProbMonad.imply_event.
Admitted. (** Level 2 *)

Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Admitted. (** Level 2 *)

```

18-21 Zicong Zhang

```coq
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
```

22-24 Andylinx

```coq
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
```

25-27 fAKe

```coq
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
```
# Auxiliary Theorem
1. ProbDistr_equiv_equiv_event

Description:
for any two distributions d1 d2, if d1 d2 are equivalent, then d1 d2 are equivalent in event.
```coq
Theorem ProbDistr_equiv_equiv_event:
  forall (d1 d2: Distr Prop),
    ProbDistr.equiv d1 d2 -> ProbDistr.equiv_event d1 d2.
```
# Note:

- fAKe: 要求：对每个 Theorem/核心 Definition 写 description 记录其直观含义。对辅助引理，注意命名规范，并且标注 "Auxiliary Theorem".

- fAKe: 开始写之前建议读一下我写的注释先，可能就不开分支了，push 的时候手动 merge 一下就好。
