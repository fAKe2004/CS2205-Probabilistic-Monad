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

18-21 Zicong Zhang (Done)

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

##### 1. ProbDistr_equiv_equiv_event

- Description:
  for any two distributions d1 d2, if d1 d2 are equivalent, then d1 d2 are equivalent in event.

```coq
Theorem ProbDistr_equiv_equiv_event:
  forall (d1 d2: Distr Prop),
    ProbDistr.equiv d1 d2 -> ProbDistr.equiv_event d1 d2.
```

##### 2.ProbDistr_biliteral_imply_event_iif_equiv_event

- Description:
  imply_event d1 d2 /\ imply_event d2 d1 <-> equiv_event d1 d2

```coq
Theorem ProbDistr_biliteral_imply_event_iif_equiv_event:
  forall d1 d2,
    (ProbDistr.imply_event d1 d2 /\ ProbDistr.imply_event d2 d1) <-> ProbDistr.equiv_event d1 d2.
```

##### 3.compute_pr_unique

result of compute_pr is uniuqe for ProbMonad.
(a similar version exists for ProbDistr)

```coq
Theorem compute_pr_unique:
  forall f r1 r2,
  ProbMonad.compute_pr f r1 ->
  ProbMonad.compute_pr f r2 ->
  r1 = r2.
```

##### 4.Forall2_equiv_g1_g2:

Apply forall a:A, g1 a == g2 a into a Forall2 form.

```coq
Lemma Forall2_equiv_g1_g2:
  forall (A B : Type) (d1 : Distr A) (d2 : list (R * Distr B)) (g1 g2 : A -> ProbMonad.M B),
    (forall a : A, g1 a == g2 a) ->
    Forall2 (fun (a : A) '(r, d) => r = d1.(prob) a /\ d ∈ (g1 a).(distr)) d1.(pset) d2 ->
    Forall2 (fun (a0 : A) '(r, d) => r = d1.(prob) a0 /\ d ∈ (g2 a0).(distr)) d1.(pset) d2.
```

##### 5.is_det_compute_pr_01

If d is a legal(to ensuer prob $\ge$ 0) deterministc distribution of Prop P.
Then compute_pr d = $\begin{cases}0&\neg P \\ 1 & P \end{cases}$

```coq
Theorem is_det_compute_pr_01:
  forall P d,
    ProbDistr.is_det P d ->
    ((~P -> ProbDistr.compute_pr d 0%R) /\
    (P-> ProbDistr.compute_pr d 1%R)).
```

##### 6.eq_dec_refl

eq_dec is a reflexive realtion and the result of eq_dec a a = left eq_refl.

```coq
Lemma eq_dec_refl: forall {A: Type} (a: A), eq_dec a a = left eq_refl.
```

##### 7.not_equal_symmetry

not_equl for Type A is symmetric , if x <> y, then y <> x.

```coq
Lemma not_equal_symmetry : forall (A : Type) (x y : A), x <> y -> y <> x.
```

##### 7.ProbDistr_equiv_event_congr

simplify the way to use transistive realtion on ProbDistr.equiv_event.

```coq
Lemma ProbDistr_equiv_event_congr :
  forall (d1 d2 d3 : Distr Prop),
    ProbDistr.equiv_event d1 d2 ->
    ProbDistr.equiv_event d2 d3 ->
    ProbDistr.equiv_event d1 d3.
```

---

# Note:

- fAKe: 要求：对每个 Theorem/核心 Definition 写 description 记录其直观含义。对辅助引理，注意命名规范，并且标注 "Auxiliary Theorem".

- fAKe: 开始写之前建议读一下我写的注释先，可能就不开分支了，push 的时候手动 merge 一下就好。
