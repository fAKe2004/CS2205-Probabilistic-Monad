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

25-27 fAKe (Done)

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

---

### level 3 partition

28-29: Zicong Zhang
```coq
Lemma bind_assoc:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).

Lemma bind_assoc_event:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M Prop),
  ProbMonad.equiv_event
    (bind (bind f g) h)
    (bind f (fun a => bind (g a) h)).

```

30-32: fAKe (Done)
```coq
Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> ProbMonad.M B),
  bind (ret a) f == f a.

Lemma bind_ret_l_event:
  forall (A: Type)
         (a: A)
         (f: A -> ProbMonad.M Prop),
  ProbMonad.equiv_event (bind (ret a) f) (f a).

Lemma bind_ret_r:
  forall (A: Type)
         (f: ProbMonad.M A),
  bind f ret == f.

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

##### 8.ProbDistr_equiv_event_congr

simplify the way to use transistive realtion on ProbDistr.equiv_event.

```coq
Lemma ProbDistr_equiv_event_congr :
  forall (d1 d2 d3 : Distr Prop),
    ProbDistr.equiv_event d1 d2 ->
    ProbDistr.equiv_event d2 d3 ->
    ProbDistr.equiv_event d1 d3.
```

##### 9. Permutation_concat_map_in_equiv
-  Description:
    Permutation L1 L2 -> In (concat (map f L1) <-> In (concat (map f L2))
```coq
Lemma Permutation_concat_map_in_equiv :
  forall (A B : Type) (f : A -> list B) (L1 L2 : list A) (x : B),
    Permutation L1 L2 ->
    (In x (concat (map f L1)) <-> In x (concat (map f L2))).
```

#### 10. Permutation_sum_distr_equiv
  Description:
    Permutation L1 L1' -> sum_distr over L1 L1' is equivalent (assume legality)
```coq
Theorem Permutation_sum_distr_equiv:
  forall (L1 L1' : list (R * Distr Prop)) (ds1 ds2 : Distr Prop),
  Permutation L1 L1'
  -> ProbDistr.sum_distr L1 ds1
  -> ProbDistr.sum_distr L1' ds2
  -> ProbDistr.legal ds1
  -> ProbDistr.legal ds2
  -> ProbDistr.equiv ds1 ds2.
```

#### 11. ProbMonad_equiv_equiv_event:

  ProbMonad.equiv f1 f2 -> ProbMonad.equiv_event f1 f2

```coq
  forall (f1 f2: ProbMonad.M Prop),
    ProbMonad.equiv f1 f2 ->
    ProbMonad.equiv_event f1 f2.
```

#### 12. Forall2_singleton_inv
  
  Extract the element in the resulting list under singleton Forall2 relation.

  `Forall2 rel [a] l -> exists b, l = [b] /\ rel a b.`

```coq
  Lemma Forall2_singleton_inv : forall A B (rel : A -> B -> Prop) (a : A) (l : list B),
  Forall2 rel [a] l -> exists b, l = [b] /\ rel a b.
```

#### 13. sum_distr_singleton_preserve:

  sum_distr over singelton with weight 1%R implies equivalence relation between input and output distribution.

  `ProbDistr.sum_distr [(1, d)] ds -> d == ds.`

```coq
Lemma sum_distr_singleton_preserve:
  forall {A: Type} (r : R) (d: Distr A) (ds : Distr A),
    r = 1%R ->
    ProbDistr.legal d ->
    ProbDistr.sum_distr [(r, d)] ds 
    -> ProbDistr.equiv d ds.
```

#### 14. forall_exists_Forall2_exists:
  construct a Forall2 list from "forall a, exists b, rel a b"

  To reuse this, you might need to move this lemma to front part of the code as its defined at tail for bind_ret_r.

```coq
Theorem forall_exists_Forall2_exists:
  forall {A B: Type} (rel: A->B->Prop) (l1: list A),
    (forall a : A, exists b : B, rel a b) -> exists l2, Forall2 rel l1 l2.
```

  Note: a similar but conditioned version may be helpful, but I don't need it, so not proven.

#### 15. is_det_prob_01

if ProbDistr.is_det a d, then:
    $d.(\text{prob})\ b = \begin{cases}1 & a=b \\ 0 & a \neq b \end{cases}$
```coq
Theorem is_det_prob_01:
  forall {A : Type} (d : Distr A) (a: A) (b: A),
    ProbDistr.is_det a d ->
    ((a = b -> d.(prob) b = 1%R) /\ (a <> b -> d.(prob) b = 0%R)).
```

#### 16. ProbDistr_sum_distr_exists
  For any list of weighted distributions, there exists a summed distribution.
```coq
Theorem ProbDistr_sum_distr_exists:
  forall {A: Type} (l: list (R * Distr A)),
    exists d, ProbDistr.sum_distr l d.
```

#### 17. ProbDistr_sum_distr_legal
  if the Forall (r, d) in l : r >= 0 /\ legal d, 
  then ds: sum_distr l ds, ds is legal.

```coq
Theorem ProbDistr_sum_distr_legal:
  forall {A: Type} (l: list (R * Distr A)) (ds: Distr A),
    Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l ->
    ProbDistr.sum_distr l ds ->
    ProbDistr.legal ds.
```

#### 18. ProbDistr_equiv_legal_congr
  if d1 ~=~ d2 -> legal d1 -> legal d2
```coq
Theorem ProbDistr_equiv_legal_congr:
  forall {A: Type} (d1 d2: Distr A),
    ProbDistr.equiv d1 d2 -> ProbDistr.legal d1 -> ProbDistr.legal d2.
```

#### 19. is_det_exists
  for any element a: A, there exists a deterministic distribution d s.t. is_det a d.
```coq

Theorem is_det_exists:
  forall {A: Type} (a: A),
    exists d: Distr A, ProbDistr.is_det a d.
```

#### 20. ProbDistr_not_in_pset_prob_0:
  if d is legal, then ~In a d.(pset) -> d.(prob) a = 0.
```coq
Theorem ProbDistr_not_in_pset_prob_0:
  forall {A: Type} (d : Distr A) (a : A),
    ProbDistr.legal d->
   ~In a d.(pset) ->  d.(prob) a = 0%R.
```

#### 21. ProbDistr_sum_distr_permutation_equiv
  Permutation L1 L1' -> sum_distr over L1 L1' is equivalent (assume legality)
```coq
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
```

#### 22. ProbDistr_sum_distr_equiv_equiv
  Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) L1 L2
    -> sum_distr L1 ~=~ sum_distr L2
```coq
Theorem ProbDistr_sum_distr_equiv_equiv:
  forall {B: Type} (L1 L2 : list (R * Distr B)) (ds1 ds2 : Distr B),
  Forall2 (fun '(r1, d1) '(r2, d2) => (r1 = r2)%R /\ ProbDistr.equiv d1 d2) L1 L2
  -> ProbDistr.sum_distr L1 ds1
  -> ProbDistr.sum_distr L2 ds2
  -> ProbDistr.equiv ds1 ds2.
```

#### 23. ProbDistr_sum_distr_legal_precondition_helper
    To convert common condition in bind f g, into precondition for sum_distr_legal
```coq
Theorem ProbDistr_sum_distr_legal_precondition_helper:
  forall {A B: Type} (f: Distr A -> Prop) (g: A -> Distr B -> Prop)  (df : Distr A) (l : list (R * Distr B)),
  Legal f ->
  (forall a : A, Legal (g a)) ->
  df ∈ f ->
  Forall2 (fun (a : A) '(r, d) => r = df.(prob) a /\ d ∈ g a) df.(pset) l ->
  Forall (fun '(r, d) => (r >= 0)%R /\ ProbDistr.legal d) l /\
  sum (map (fun '(r, d) => r) l) = 1%R.
```
---

# Note:

- fAKe: 要求：对每个 Theorem/核心 Definition 写 description 记录其直观含义。对辅助引理，注意命名规范，并且标注 "Auxiliary Theorem".

- fAKe: 开始写之前建议读一下我写的注释先，可能就不开分支了，push 的时候手动 merge 一下就好。

- <font color = "crimson"> January 6th: IMPORTANT UPDATE </font> fAKe
1. 对 sum_distr 做了 legal 要求的修改。
```coq
  sum_legal:
    legal d0;
```
2. 对 ProbMonad 做了 legal_congr 的修改。
```coq
  Legal_congr: forall d1 d2, ProbDistr.equiv d1 d2 -> d1 ∈ f -> d2 ∈ f;
```

也就是说 ProbMonad.(distr) 对于 ProbDistr.equiv 是封闭的，这是一个合理的要求，不然后面命题证明不了。

以上两个修改造成前面少数命题证明挂了，已经用 NEED FIX 标出，相应的同学稍微修一下，应该不是大问题。

- January 9th fAKe,
  写好了 bind_ret_r 的证明，也算是稍微搞懂了点怎么证明 sum_distr 相关的性质了。建议各位先读一下 bint_ret_l 之后的关于 bind_ret_r 的证明，理解一下怎么处理 Forall2.

  - __ret_legal 已经 fix 了。

  - 听说 Always_consq 有点问题，暂停。

  - 把 sum_distr_legal 的要求暂时弱化成了 sum_pset_no_dup.

---

## Correctness Fix Summary:

#### 1. ProbDistr.compute_pr:
```coq
Definition compute_pr (d: Distr Prop) (r: R): Prop :=
  exists (l: list Prop),
    NoDup l /\
    (forall P, In P l <-> In P d.(pset) /\ P) /\
    sum_prob l d.(prob) = r.
```

add NoDup requirement to l

#### 2. ProbDistr.imply_event/equiv_event:
```coq
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
```
redefined solely with compute_pr

#### 3. ProbMonad.Legal

```coq
Record Legal {A: Type} (f: Distr A -> Prop): Prop := {
  (* exists a unique legal Distr d in f *)
  Legal_exists: exists d, d ∈ f;
  Legal_legal: forall d, d ∈ f -> ProbDistr.legal d;
  Legal_unique: forall d1 d2, d1 ∈ f -> d2 ∈ f -> ProbDistr.equiv d1 d2;
  (* congruence under ProbDistr.equiv*)
  Legal_congr: forall d1 d2, ProbDistr.equiv d1 d2 -> d1 ∈ f -> d2 ∈ f;
}.
```

add Legal_congr requirement. 
(this is a natural and reasonable fix, otherwise bind_ret_l would be unprovable. )

#### 4. ProbDistr.sum_distr

```coq
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
```

add NoDup requirement to resulting distribution's pset. (necessiated by a bunch of bind'
s legality related statements)