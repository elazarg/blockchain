Require Import List.

Import ListNotations.

Require Import Nat.
Require Import Arith.

Section SKIPN.

Variables (A : Type).

(* firstn_nil: forall (A : Type) (n : nat), firstn n nil = nil *)
Lemma skipn_nil : forall (n : nat),
  skipn n nil = (nil : list A).
Proof. destruct n; reflexivity. Qed.

Lemma skipn_nil_length : forall (n : nat) (ws : list A),
  skipn n ws = nil -> length ws <= n.
Proof.
  induction n; intros; simpl in H.
  - subst ws. apply Peano.le_0_n.
  - destruct ws.
    + apply Peano.le_0_n.
    + apply IHn in H.
      apply Peano.le_n_S, H.
Qed.

(*

firstn_cons:  forall (A : Type) (n : nat) (a : A) (l : list A),
  firstn (S n) (a :: l) = a :: firstn n l
firstn_O: forall (A : Type) (l : list A), firstn 0 l = nil
firstn_le_length: forall (A : Type) (n : nat) (l : list A), length (firstn n l) <= n
firstn_length_le:  forall (A : Type) (l : list A) (n : nat),
  n <= length l -> length (firstn n l) = n
firstn_firstn:  forall (A : Type) (l : list A) (i j : nat),
  firstn i (firstn j l) = firstn (min i j) l

removelast_firstn:  forall (A : Type) (n : nat) (l : list A),
  n < length l -> removelast (firstn (S n) l) = firstn n l
firstn_removelast:  forall (A : Type) (n : nat) (l : list A),
  n < length l -> firstn n (removelast l) = firstn n l
*)

(*
firstn_all2: forall (A : Type) (n : nat) (l : list A), length l <= n -> firstn n l = l
*)
Lemma skipn_lt : forall (n : nat) (l : list A),
  skipn n l <> nil -> n < length l.
Proof.
  induction n; intros.
  - destruct (zerop (length l)).
    + apply length_zero_iff_nil in e.
      contradiction.
    + assumption.
  - destruct l; simpl in H.
    + contradiction.
    + apply IHn in H.
      apply lt_n_S, H.
Qed.

Lemma skipn_head_lt : forall (n : nat) (l : list A) (x : A) (xs : list A),
  skipn n l = x::xs -> n < length l.
Proof.
  intros.
  assert (skipn n l <> nil).
    intro. rewrite -> H0 in H. inversion H.
  apply skipn_lt.
  assumption.
Qed.

(* firstn_length:  forall (A : Type) (n : nat) (l : list A),
  length (firstn n l) = min n (length l) *)
Lemma skipn_length: forall (n : nat) (l : list A),
  length (skipn n l) <= length l.
Proof.
  induction n; auto.
  intros.
  destruct l; auto.
  simpl.
  apply le_S.
  apply IHn.
Qed.

Lemma skipn_not_lengthen : forall (n : nat) (a : A) (l : list A),
  skipn n l <> a::l.
Proof.
  unfold not.
  intros. assert (length (skipn n l) <= length l) by (apply skipn_length).
  rewrite -> H in H0. simpl in H0.
  apply le_S_gt in H0.
  apply (gt_irrefl _ H0).
Qed.

Lemma skipn_short : forall (l l': list A),
  skipn (length l) (l ++ l') = l'.
Proof.
  induction l.
  intros. reflexivity.
  assumption.
Qed.
(* 
firstn_all: forall (A : Type) (l : list A), firstn (length l) l = l
firstn_all2: forall (A : Type) (n : nat) (l : list A), length l <= n -> firstn n l = l 
*)
Lemma skipn_head_all : forall (n : nat) (a : A) (l l': list A),
  skipn n (l ++ (a::l')) = (a::l') -> n = length l.
Proof.
  induction n; intros; simpl in H.
  - rewrite <- app_nil_l in H.
    apply app_inv_tail in H.
    subst l.
    reflexivity.
  - destruct l.
    + apply skipn_not_lengthen in H. contradiction.
    + simpl. f_equal. apply IHn in H. assumption.
Qed.

(* firstn_app:  forall (A : Type) (n : nat) (l1 l2 : list A),
  firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2
firstn_app_2:  forall (A : Type) (n : nat) (l1 l2 : list A),
  firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2 *)

Lemma skipn_app : forall (a : A) (l l' : list A),
  skipn (length l) (l ++ (a::l')) = (a::l').
Proof. induction l; auto. Qed.

Lemma skipn_succ : forall {T} n l (x : T) xs,
  x :: xs = skipn n l -> xs = skipn (1 + n) l.
Proof.
  induction n; intros; destruct l; (try rewrite -> skipn_nil' in H; inversion H).
  + inversion H.
    reflexivity.
  + simpl in H.
    apply IHn in H.
    subst xs.
    destruct l; reflexivity.
Qed.

End SKIPN.

Lemma app_app : forall {A : Type} (x y: list A) (a : A),
  x ++ a::y = (x ++ [a]) ++ y.
Proof.
  induction x; auto.
  intros.
  simpl.
  rewrite <- IHx.
  reflexivity.
Qed.

Lemma cons_inj : forall {A : Type} (l : list A) (a : A),
  l <> a::l.
Proof.
  unfold not.
  induction l; intros; inversion H.
  apply IHl in H2.
  assumption.
Qed.
