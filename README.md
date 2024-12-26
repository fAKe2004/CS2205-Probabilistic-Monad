# CS2205-Probabilistic-Monad

Project repo for CS2205 ProbMonad

level 1 partition

1-4 fAKe (Done)

6-8 Andylinx

```coq
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
```

9-11 Zicong Zhang

(9-10 finished)

left :

```coq
Lemma __ret_Legal {A: Type}: forall a: A, Legal (__ret a).
Admitted.
```

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

# Note:

- fAKe: 没怎么看懂 imply-event 到底讲了什么，如果有更直观的理解请写进 description 部分。

- fAKe: 要求：对每个 Theorem/核心 Definition 写 description 记录其直观含义。对辅助引理，注意命名规范，并且标注 "Auxiliary Theorem".

- fAKe: 开始写之前建议读一下我写的注释先，可能就不开分支了，push 的时候手动 merge 一下就好。
