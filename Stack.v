Require Import Bool.
Require Import List.
Require Import Nat.
Require Import Arith.

Import ListNotations.

(* Project modules *)
Require Import ListUtils.
Require Import Instructions.
Require Import Word.

Definition dup (n : nat) (ws : list word) : option (list word) :=
   match List.nth_error ws n with
     | Some v => Some (v::ws)
     | None => None
   end.

Definition exec_so_instr (i : so_instruction) (st : list word) : option (list word) :=
  match i, st with
    | I_OP1 op, w::ws => Some (eval_op1 op w::ws)
    | I_OP1 _, nil => None
    | I_OP2 op, (w::w0::ws) => Some (eval_op2 op w w0::ws)
    | I_OP2 _, _ => None
    | I_OP3 op, (w::w0::w1::ws) => Some (eval_op3 op w w0 w1::ws)
    | I_OP3 _, _ => None
    | I_POP, (w::ws) => Some ws
    | I_POP, _ => None
    | I_PUSH item, ws  => Some (item::ws)
    | I_DUP n _, ws => dup n ws
    | I_SWAP n _, ws => swap n ws
  end.

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

Theorem exec_so_nice : forall i st st',
  exec_so_instr i st = Some st' ->
    let d := delta (I_STACK_ONLY i) in
    let a := alpha (I_STACK_ONLY i) in
    st' = firstn a st' ++ skipn d st.
Proof.
  intros.
  destruct (exec_so_instr i st) eqn:Q; inversion H.
  subst l.
  destruct i.
  + (* I_OP1 *)
    destruct st; inversion Q.
    reflexivity.
  + (* I_OP2 *)
    destruct st eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    inversion Q.
    reflexivity.
  + (* I_OP3 *)
    destruct st eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    destruct l0; inversion Q.
    reflexivity.
  + (* I_POP *)
    destruct st eqn:?; inversion Q.
    reflexivity.
  + (* I_PUSH *)
    inversion Q.
    reflexivity.
  + (* I_DUP *)
    subst a d.
    unfold exec_so_instr in Q. unfold dup in Q.
    destruct (nth_error st n) eqn:NE; inversion Q.
    destruct st; auto.
    simpl. f_equal. f_equal.
    symmetry.
    apply firstn_skipn.
  + (* I_SWAP *)
    subst a d.
    apply swap_alpha_2n_delta_2n in Q.
    rewrite <- (firstn_skipn (S (S n)) st') at 1.
    f_equal.
    symmetry.
    assumption.
Qed.

Definition SUB_BOUND := 1023.
Definition BOUND := S SUB_BOUND.
Definition inbounds n : Prop := n < BOUND.
Definition noflow (xs : list word) : Prop := inbounds (length xs).
