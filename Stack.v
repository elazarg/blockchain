Require Import Bool.
Require Import List.
Require Import Nat.
Require Import Arith.

Import ListNotations.

(* Project modules *)
Require Import ListUtils.

Definition dup {T: Type} (n : nat) (ws : list T) : option (list T) :=
   match List.nth_error ws n with
     | Some v => Some (v::ws)
     | None => None
   end.

Definition apply_1 {T} (f: T -> T) xs :=
  match xs with
    | a::xs => Some (f a::xs)
    | nil => None
  end.

Definition apply_2 {T} (f: T -> T -> T) xs :=
  match xs with
    | a::b::xs => Some (f a b::xs)
    | _ => None
  end.

Definition apply_3 {T} (f: T -> T -> T -> T) xs :=
  match xs with
    | a::b::c::xs => Some (f a b c::xs)
    | _ => None
  end.

Section SWAP.

Definition swap {T : Type} (n : nat) (ws : list T) : option (list T) :=
   match skipn (1+n) ws, firstn (1+n) ws with
     | w1 :: l1, w0 :: l0 => Some ((w1 :: l0) ++ w0 :: l1)
     | _, _ => None
   end.

Variable (T : Type).

Lemma swap_same_length : forall (w0 w1 : T) (l0 l1 : list T),
  length ((w0 :: l0) ++ w1 :: l1) = length ((w1 :: l0) ++ w0 :: l1).
Proof.
  intros.
  rewrite -> app_length.
  rewrite -> app_length.
  reflexivity.
Qed.

Lemma swap_eq : forall (n : nat) (ws ws' : list T),
  swap n ws = Some ws' ->
  length ws = length ws'.
Proof.
  intros n ws ws'.
  intros.
  unfold swap in H.
  destruct (skipn (1+n) ws) eqn:S. discriminate H.
  destruct (firstn (1+n) ws) eqn:F. discriminate H.
  rewrite <- (firstn_skipn (1+n) ws).
  inversion H.
  rewrite -> F, S.
  rewrite -> app_comm_cons.
  apply swap_same_length.
Qed.

Lemma swap_long : forall (n : nat) (ws ws' : list T),
  swap n ws = Some ws' ->
  (1+n) < length ws.
Proof.
  intros. simpl.
  unfold swap in H.
  destruct (skipn (1 + n) ws) eqn:Q. inversion H.
  destruct (firstn (1 + n) ws). inversion H.
  apply skipn_head_lt in Q.
  assumption.
Qed.

Lemma swap_skipn_length : forall (w0 w1 : T) (l0 l1 : list T),
  swap (length l0) ((w0 :: l0) ++ w1 :: l1) = Some ((w1 :: l0) ++ w0 :: l1).
Proof.
  intros.
  unfold swap.
  assert (1 + length l0 = length (w0::l0)) by reflexivity.
  rewrite -> H.
  rewrite -> firstn_app, firstn_all, minus_diag.
  rewrite -> skipn_app, app_nil_r.
  reflexivity.
Qed.

Lemma swap_correct : forall (n : nat) (ws ws' : list T),
  swap n ws = Some ws'
  -> exists w0 w1 l0 l1, ws = (w0::l0) ++ (w1::l1) /\ ws' = (w1::l0) ++ (w0::l1).
Proof.
  intros. unfold swap in H.
  assert ( firstn (1 + n) ws ++ skipn (1 + n) ws = ws) by apply firstn_skipn.
  destruct ws eqn:Q. inversion H.
  simpl in *.
  destruct (skipn n l).
  - inversion H.
  - inversion H0.
    exists t, t0, (firstn n l), (skipn (1+n) l).
    assert (FS: firstn n l ++ skipn n l = l) by apply firstn_skipn.
    split; [idtac | inversion H];
      do 3 f_equal;
      rewrite <- FS in H2 at 2;
      apply app_inv_head, skipn_succ in H2;
      assumption.
Qed.

End SWAP.

Lemma swap_alpha_2n_delta_2n : forall {T : Type} (n : nat) (ws ws' : list T),
  swap n ws = Some ws'
  -> skipn (2 + n) ws = skipn (2 + n) ws'.
Proof.
  intros.
  unfold swap in H.
  assert (FS: firstn (1+n) ws ++ skipn (1+n) ws = ws) by apply firstn_skipn.
  destruct (skipn (1 + n) ws) eqn:SKIP. inversion H.
  destruct (firstn (1 + n) ws). inversion H.

  rewrite -> app_app in H.
  inversion H.
  subst ws' ws.
  rewrite -> app_app.
  rewrite -> app_comm_cons at 1.
  rewrite <- app_comm_cons at 1.

  Ltac skip x fstn SKIP := replace (2 + x) with (length fstn) at 1 by (
    apply skipn_head_all in SKIP;
    rewrite -> app_comm_cons, app_length, plus_comm;
    inversion SKIP;
    reflexivity
  ).
  skip n (t0 :: l0 ++ [t]) SKIP. rewrite -> skipn_short.
  skip n (t :: l0 ++ [t0]) SKIP. rewrite -> skipn_short.
  reflexivity.
Qed.
