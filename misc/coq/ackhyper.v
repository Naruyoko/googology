(** A practice of Coq. Defines Ackermann function and hyperoperators and proves equality (in some way) *)

Require Import Coq.PArith.BinPos.
Require Import Arith.

Fixpoint Ack (x : nat) : nat -> nat :=
  fix Ack_aux (y : nat) : nat :=
  match x with
  | 0 => S y
  | S x' =>
    match y with
    | 0 => Ack x' 1
    | S y' => Ack x' (Ack_aux y')
    end
  end.

Compute Ack 3 3.

Fixpoint hyper (c : nat) : nat -> nat -> nat :=
  fix hyper_aux (a b : nat) : nat :=
  match c with
  | 0 => S b
  | S c' =>
    match b with
    | 0 =>
      match c with
      | 1 => a
      | 2 => 0
      | _ => 1
      end
    | S b' => hyper c' a (hyper_aux a b')
    end
  end.

Compute hyper 3 3 3.

Lemma Ack_0_eq_succ : forall y, Ack 0 y = S y.
Proof.
  destruct y; auto.
Qed.

Lemma Ack_succ_0 : forall x, Ack (S x) 0 = Ack x 1.
Proof.
  reflexivity.
Qed.

Lemma Ack_succ_succ : forall x y, Ack (S x) (S y) = Ack x (Ack (S x) y).
Proof.
  reflexivity.
Qed.

Lemma hyper_succ_any_succ : forall c a b, hyper (S c) a (S b) = hyper c a (hyper (S c) a b).
Proof.
  reflexivity.
Qed.

Lemma hyper_succsucc_any_1 : forall c a, hyper (S (S c)) a 1 = a.
Proof.
  induction c; auto.
Qed.

Lemma hyper_0_eq_succ : forall a b, hyper 0 a b = S b.
Proof.
  destruct b; auto.
Qed.

Lemma hyper_1_eq_add : forall a b, hyper 1 a b = a + b.
Proof.
  induction b.
  - auto.
  - rewrite hyper_succ_any_succ. rewrite hyper_0_eq_succ. rewrite IHb. auto.
Qed.

Lemma hyper_2_eq_mul : forall a b, hyper 2 a b = a * b.
Proof.
  induction b.
  - auto.
  - rewrite hyper_succ_any_succ. rewrite hyper_1_eq_add. rewrite IHb. ring.
Qed.

Lemma hyper_3_eq_pow : forall a b, hyper 3 a b = a ^ b.
Proof.
  induction b.
  - auto.
  - rewrite hyper_succ_any_succ.
    rewrite hyper_2_eq_mul.
    rewrite IHb.
    rewrite Nat.pow_succ_r.
    + reflexivity.
    + exact (Peano.le_0_n _).
Qed.

Lemma hyper_succ_2_2 : forall c, hyper (S c) 2 2 = 4.
Proof.
  induction c.
  - auto.
  - rewrite hyper_succ_any_succ. rewrite hyper_succsucc_any_1. rewrite IHc. reflexivity.
Qed.

Lemma strict_mono_ge_add_input_0 : forall f : nat -> nat, (forall x y, x < y -> f x < f y) -> forall x, x + f 0 <= f x.
Proof.
  induction x.
  - auto.
  - refine (Nat.le_trans _ (S (f x)) _ _ _).
    + rewrite Nat.add_succ_l. rewrite <- Nat.succ_le_mono. assumption.
    + rewrite Nat.le_succ_l. auto.
Qed.

Lemma strict_mono_next_incl_strict_mono : forall f : nat -> nat, (forall x, f x < f (S x)) -> forall x y, x < y -> f x < f y.
Proof.
  intros f H x y Hx.
  apply lt_le_S in Hx.
  revert y Hx.
  apply Nat.right_induction.
  - intuition.
  - exact (H _).
  - intros y Hx IHy. exact (Nat.lt_trans _ (f y) _ IHy (H _)).
Qed.

Lemma hyper_succsuccsucc_succsucc_strict_mono: forall c a b d, b < d -> let f := fun x => hyper (S (S c)) (S (S a)) x in f b < f d.
Proof.
  intros c a.
  induction c.
  - intros b d H f.
    subst f.
    repeat rewrite hyper_2_eq_mul.
    rewrite <- (Nat.mul_lt_mono_pos_l _ _ _ (Nat.lt_0_succ _)).
    assumption.
  - set (hyper (S (S (S c))) (S (S a))) as f.
    assert (forall b, f b < f (S b)) as mono_next.
    {
      set (hyper (S (S c)) (S (S a))) as f' in IHc.
      intro b.
      unfold f.
      rewrite hyper_succ_any_succ.
      destruct c.
      - rewrite hyper_2_eq_mul.
        rewrite Nat.mul_succ_l.
        apply Nat.lt_add_pos_l.
        rewrite Nat.lt_0_mul'.
        split.
        + exact (Nat.lt_0_succ _).
        + rewrite hyper_3_eq_pow.
          rewrite <- Nat.neq_0_lt_0.
          apply Nat.pow_nonzero.
          discriminate.
      - fold f f'.
        refine (Nat.lt_le_trans _ (f b + f' 0) _ _ _).
        + apply Nat.lt_add_pos_r. exact (Nat.lt_0_succ _).
        + apply strict_mono_ge_add_input_0. assumption.
    }
    exact (strict_mono_next_incl_strict_mono f mono_next).
Qed.

Lemma hyper_succsuccsucc_succsucc_gt_right : forall c a b, hyper (S (S (S c))) (S (S a)) b > b.
Proof.
  intros c a.
  induction c; [intro | induction b].
  - rewrite hyper_3_eq_pow.
    apply Nat.pow_gt_lin_r.
    intuition.
  - compute. auto.
  - rewrite hyper_succ_any_succ.
    set (hyper (S (S (S (S c)))) (S (S a))) as f.
    fold f in IHb.
    set (hyper (S (S (S c))) (S (S a))) as f'.
    fold f' in IHc.
    refine (Nat.le_lt_trans _ (f b) _ _ _).
    + apply lt_le_S. assumption.
    + exact (IHc _).
Qed.

Lemma Ack_succ_as_hyper : forall x y, Ack (S x) y = hyper (S x) 2 (y + 3) - 3.
Proof.
  induction x; intro; induction y.
  - exact (eq_refl _).
  - rewrite hyper_1_eq_add.
    rewrite hyper_1_eq_add in IHy.
    assert (forall z, 2 + (z + 3) - 3 = 2 + z) as simplified.
    {
      intro.
      rewrite (Nat.add_comm z 3).
      simpl.
      reflexivity.
    }
    rewrite Ack_succ_succ.
    rewrite Ack_0_eq_succ.
    rewrite IHy.
    repeat rewrite simplified.
    simpl.
    reflexivity.
  - rewrite Ack_succ_0.
    rewrite IHx.
    rewrite Nat.add_0_l.
    rewrite (hyper_succ_any_succ (S x)).
    rewrite hyper_succ_2_2.
    reflexivity.
  - rewrite Ack_succ_succ.
    rewrite IHy.
    rewrite IHx.
    assert (forall z, 3 <= hyper (S (S x)) 2 (z + 3)) as lower_bound.
    {
      intro.
      destruct x.
      - rewrite hyper_2_eq_mul. simpl. intuition.
      - refine (Nat.le_trans _ (z + 4) _ _ _).
        + intuition.
        + rewrite Nat.add_succ_r.
          rewrite Nat.le_succ_l.
          exact (hyper_succsuccsucc_succsucc_gt_right _ _ _).
    }
    rewrite (Nat.sub_add _ _ (lower_bound _)).
    rewrite Nat.add_succ_l.
    rewrite hyper_succ_any_succ.
    reflexivity.
Qed.

Theorem Ack_as_hyper : forall x y, Ack x y =
  match x with
  | 0 => S y
  | _ => hyper x 2 (y + 3) - 3
  end.
Proof.
  destruct x.
  - exact Ack_0_eq_succ.
  - exact (Ack_succ_as_hyper _).
Qed.
