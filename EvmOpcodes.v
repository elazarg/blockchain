(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)
Require Import Bool.
Require Import List.
Require Import Nat.
Require Import EqNat.
Require Import Arith.
Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import PeanoNat.

Definition byte := nat.
Definition byte32 := {items : list byte | 0 < length items /\ length items <= 32}.
Definition word := nat.

Inductive op1 : Type :=
  | OP_ISZERO
  | OP_NOT
.

Inductive op2 : Type :=
  | OP_ADD
  | OP_MUL
  | OP_SUB
  | OP_DIV
  | OP_SDIV
  | OP_MOD
  | OP_SMOD
  | OP_EXP
  | OP_SIGNEXTEND
  | OP_LT
  | OP_GT
  | OP_SLT
  | OP_SGT
  | OP_EQ
  | OP_AND
  | OP_OR
  | OP_XOR
  | OP_BYTE
.

Inductive op3 : Type :=
  | OP_ADDMOD
  | OP_MULMOD
.

Inductive so_instruction : Type :=
  | I_STOP
  | I_OP1 : op1 -> so_instruction
  | I_OP2 : op2 -> so_instruction
  | I_OP3 : op3 -> so_instruction
  | I_POP
  | I_PUSH : word -> so_instruction (* coerced from a list of 1-32 bytes, big endian; the rest is zero *)
  | I_DUP (n : nat) : n < 16 -> so_instruction (* n is one less than DUPN *)
  | I_SWAP (n : nat) : n < 16 -> so_instruction (* n is one less than SWAPN *)
.

Inductive mem_instruction : Type :=
  | I_MLOAD
  | I_MSTORE
  | I_MSTORE8
.

Inductive storage_instruction : Type :=
  | I_SLOAD
  | I_SSTORE
.

Inductive instruction : Type :=
  | I_STACK_ONLY : so_instruction -> instruction
  | I_SHA3

  | I_ADDRESS
  | I_BALANCE
  | I_ORIGIN
  | I_CALLER
  | I_CALLVALUE
  | I_CALLDATALOAD
  | I_CALLDATASIZE
  | I_CALLDATACOPY
  | I_CODESIZE
  | I_CODECOPY
  | I_GASPRICE
  | I_EXTCODESIZE
  | I_EXTCODECOPY

  | I_BLOCKHASH
  | I_COINBASE
  | I_TIMESTAMP
  | I_NUMBER
  | I_DIFFICULTY
  | I_GASLIMIT

  | I_MEMINS : mem_instruction -> instruction
  | I_STORINS : storage_instruction -> instruction

  | I_JUMP
  | I_JUMPI
  | I_PC

  | I_MSIZE
  | I_GAS
  | I_JUMPDEST (* NO-OP - mark as label *)

  | I_LOG : nat (* 0-4 *) -> instruction

  | I_CREATE
  | I_CALL
  | I_CALLCODE
  | I_RETURN
  | I_DELEGATECALL
  | I_SUICIDE
.


Definition delta_alpha (i: instruction) : nat*nat :=
  match i with
    | I_STACK_ONLY I_STOP => (0, 0)
    | I_STACK_ONLY (I_OP1 _) => (1, 1)
    | I_STACK_ONLY (I_OP2 _) => (2, 1)
    | I_STACK_ONLY (I_OP3 _) => (3, 1)
    | I_STACK_ONLY I_POP => (1, 0)
    | I_STACK_ONLY (I_PUSH _) => (0, 1)
    | I_STACK_ONLY (I_DUP n _) => (1 + n, 2 + n)
    | I_STACK_ONLY (I_SWAP n _) => (2 + n, 2 + n)
    | I_SHA3 => (2, 1)

    | I_ADDRESS => (0, 1)
    | I_BALANCE => (1, 1)
    | I_ORIGIN => (0, 1)
    | I_CALLER => (0, 1)
    | I_CALLVALUE => (0, 1)
    | I_CALLDATALOAD => (1, 1)
    | I_CALLDATASIZE => (0, 1)
    | I_CALLDATACOPY => (3, 0)
    | I_CODESIZE => (0, 1)
    | I_CODECOPY => (3, 0)
    | I_GASPRICE => (0, 1)
    | I_EXTCODESIZE => (1, 1)
    | I_EXTCODECOPY => (4, 0)

    | I_BLOCKHASH => (1, 1)
    | I_COINBASE => (0, 1)
    | I_TIMESTAMP => (0, 1)
    | I_NUMBER => (0, 1)
    | I_DIFFICULTY => (0, 1)
    | I_GASLIMIT => (0, 1)

    | I_MEMINS I_MLOAD => (1, 1)
    | I_MEMINS I_MSTORE => (2, 0)
    | I_MEMINS I_MSTORE8 => (2, 0)
    | I_STORINS I_SLOAD => (1, 1)
    | I_STORINS I_SSTORE => (2, 0)

    | I_JUMP => (1, 0)
    | I_JUMPI => (2, 0)
    | I_PC => (0, 1)

    | I_MSIZE => (0, 1)
    | I_GAS => (0, 1)
    | I_JUMPDEST  => (0, 0) (* NO-OP - mark as label *)

    | I_LOG n => (n + 2, 0)

    | I_CREATE => (3, 1)
    | I_CALL => (7, 1)
    | I_CALLCODE => (7, 1)
    | I_RETURN => (2, 0)
    | I_DELEGATECALL => (6, 1)
    | I_SUICIDE => (1, 10)
  end.

Definition delta (i: instruction) : nat := fst (delta_alpha i).
Definition alpha (i: instruction) : nat := snd (delta_alpha i).

Parameter SUB_BOUND : nat.
Definition BOUND := S SUB_BOUND.

(** The stack is represented as a Coq [list word]
    plus a proof that its lenth is smaller than BOUND *)
Record stack_t: Type := mkstack {
  stckval: list word; 
  stcksize: length stckval < BOUND
}.

Lemma pop_lt : forall {w : word} {ws: list word}, length (w :: ws) < BOUND -> length ws < BOUND.
Proof.
  intros.
  exact (Nat.lt_lt_succ_r (length ws) SUB_BOUND (lt_S_n (length ws) SUB_BOUND H)).
Qed.

Definition eval_op1 (op : op1) (c : word) : word :=
  match op with
    | OP_ISZERO => if c then 0 else 1
    | OP_NOT => if c then 0 else 1
  end.

Definition eval_op2 (op : op2) (c1 c2 : word) : word :=
  match op with
    | OP_ADD => c1 + c2
    | OP_MUL => c1 * c2
    | OP_SUB => c1 - c2
    | OP_DIV => c1 / c2
    | _ => c1 (*
    | OP_SDIV
    | OP_MOD
    | OP_SMOD
    | OP_EXP
    | OP_SIGNEXTEND
    | OP_LT
    | OP_GT
    | OP_SLT
    | OP_SGT
    | OP_EQ
    | OP_AND
    | OP_OR
    | OP_XOR
    | OP_BYTE *)
  end.

Definition eval_op3 (op : op3) (c1 c2 c3 : word) : word :=
  match op with
    | OP_ADDMOD => c1
    | OP_MULMOD => c1
  end.

Variable coerce_to_word : byte32 -> word.

Definition option_mkstack (st : list word) : option stack_t :=
  match le_lt_dec BOUND (length st) with
    | right LEN => Some (mkstack st LEN)
    | left _ => None
  end.

Definition inbounds n : Prop := n < BOUND.
Definition noflow (xs : list word) : Prop := inbounds (length xs).

Definition dup (n : nat) (ws : list word) : option stack_t :=
   match List.nth_error ws n with
     | Some v => option_mkstack (v::ws)
     | None => None
   end.

Definition erased_swap (n : nat) (ws : list word) : option (list word) :=
   match skipn (1+n) ws, firstn (1+n) ws with
     | w1 :: l1, w0 :: l0 => Some ((w1 :: l0) ++ w0 :: l1)
     | _, _ => None
   end.


Lemma swap_same_length : forall {T} (w0 w1 : T) l0 l1,
  length ((w0 :: l0) ++ w1 :: l1) = length ((w1 :: l0) ++ w0 :: l1).
Proof.
  intros.
  rewrite -> app_length.
  rewrite -> app_length.
  reflexivity.
Qed.

Lemma erased_swap_eq : forall (n : nat) (ws ws' : list word),
  erased_swap n ws = Some ws' ->
  length ws = length ws'.
Proof.
  intros n ws ws'.
  intros.
  unfold erased_swap in H.
  destruct (skipn (1+n) ws) eqn:S. discriminate H.
  destruct (firstn (1+n) ws) eqn:F. discriminate H.
  rewrite <- (firstn_skipn (1+n) ws).
  inversion H.
  rewrite -> F, S.
  rewrite -> app_comm_cons.
  apply swap_same_length.
Qed.

Lemma skipn_le : forall {T} (n : nat) (ws : list T),
  skipn n ws <> nil -> n < length ws.
Proof.
  induction n.
  intros. pose (zerop (length ws)). destruct s.
    apply length_zero_iff_nil in e. contradiction.
    assumption.
  intros.
  destruct ws. simpl in H. contradiction.
  simpl in H. apply IHn in H. simpl.
  apply lt_n_S.
  assumption.
Qed.

Lemma skipn_le' : forall {T} (n : nat) (ws : list T) x xs,
  skipn n ws = x::xs -> n < length ws.
Proof.
  intros.
  assert (skipn n ws <> nil).
    intro. rewrite -> H0 in H. inversion H.
  apply skipn_le.
  assumption.
Qed.

Lemma skipn_res_shorter: forall {T} (n : nat) (ws : list T),
  length (skipn n ws) <= length ws.
Proof.
  induction n;  auto.
  intros. destruct ws; auto.
  simpl.
  apply le_S.
  apply IHn.
Qed.

Lemma skipn_not_lengthen : forall {T} (n : nat) (ws : list T) w,
  skipn n ws <> w::ws.
Proof.
  unfold not.
  intros. assert (length (skipn n ws) <= length ws) by (apply skipn_res_shorter).
  rewrite -> H in H0. simpl in H0.
  apply le_S_gt in H0.
  apply (gt_irrefl _ H0).
Qed.

Lemma skipn_short : forall {T} (xs : list T) ys,
  skipn (length xs) (xs ++ ys) = ys.
Proof.
  induction xs.
  intros. reflexivity.
  simpl. assumption.
Qed.

Lemma cons_inj : forall {T} xs (x: T),
  xs <> x::xs.
Proof.
  unfold not.
  induction xs.
  intros. inversion H.
  intros. inversion H. apply IHxs in H2. assumption.
Qed.

Lemma skipn_short1 : forall {T} n  (xs : list T) y ys,
  skipn n (xs ++ (y::ys)) = (y::ys) -> n = length xs.
Proof.
  induction n.
  intros. simpl in H. rewrite <- app_nil_l in H. apply app_inv_tail in H. subst xs. reflexivity. 
  intros.
  destruct xs. simpl in H. apply skipn_not_lengthen in H. contradiction.

  simpl in H. simpl. f_equal. apply IHn in H. assumption.
Qed.

Lemma skipn_app : forall {T} (xs : list T) y ys,
  skipn (length xs) (xs ++ (y::ys)) = (y::ys).
Proof.
  induction xs.
  intros. reflexivity.
  intros.
  simpl. apply IHxs.
Qed.


Lemma erased_swap_long : forall (n : nat) (ws ws' : list word),
  erased_swap n ws = Some ws' ->
  (1+n) < length ws.
Proof.
  intros. simpl.
  unfold erased_swap in H.
  destruct (skipn (1 + n) ws) eqn:Q. inversion H.
  destruct (firstn (1 + n) ws). inversion H.
  apply skipn_le' in Q.
  assumption.
Qed.

Lemma erased_swap_skipn : forall w0 w1 l0 l1,
  erased_swap (length l0) ((w0 :: l0) ++ w1 :: l1) = Some ((w1 :: l0) ++ w0 :: l1).
Proof.
  intros.
  unfold erased_swap.
  assert (1 + length l0 = length (w0::l0)) by reflexivity.
  rewrite -> H.
  rewrite -> firstn_app, firstn_all, minus_diag.
  rewrite -> skipn_app, app_nil_r.
  reflexivity.
Qed.

Lemma skipn_nil : forall {T} (n : nat) (ws : list T),
  skipn n ws = nil -> length ws <= n.
Proof.
  induction n.
  intros. simpl in H. subst ws. auto.
  intros. simpl in H. destruct ws. apply Peano.le_0_n.
  simpl. apply IHn in H. apply Peano.le_n_S, H.
Qed.

Lemma skipn_nil' : forall {T} (n : nat),
  skipn n nil = (nil : list T).
Proof.
  destruct n; reflexivity.
Qed.

Lemma erased_swap_long' : forall (n : nat) (ws : list word),
  1+n < length ws -> erased_swap n ws <> None.
Proof.
  unfold not.
  intros.
  unfold erased_swap in H0.
  destruct (firstn (1 + n)) eqn:Q.
  +  assert (1 + n <= length ws). apply lt_le_S, Nat.lt_succ_l. assumption.
     apply firstn_length_le in H1.
     rewrite -> Q in H1. inversion H1.
  +
    destruct (skipn (1 + n) ws) eqn:Q1.
    apply skipn_nil in Q1. apply lt_not_le in H. contradiction.
    inversion H0.
Qed.

Lemma skipn_succ : forall {T} n l (x : T) xs,
  x :: xs = skipn n l -> xs = skipn (1 + n) l.
Proof.
  induction n; intros; destruct l; (try rewrite -> skipn_nil' in H; inversion H).
  + simpl. inversion H. reflexivity.
  + simpl in H. apply IHn in H. subst xs. destruct l; reflexivity.
Qed.

Lemma erased_swap_correct : forall (n : nat) (ws ws' : list word),
  erased_swap n ws = Some ws'
  -> exists w0 w1 l0 l1, ws = (w0::l0) ++ (w1::l1) /\ ws' = (w1::l0) ++ (w0::l1).
Proof.
  intros. unfold erased_swap in H.
  assert ( firstn (1 + n) ws ++ skipn (1 + n) ws = ws) by apply firstn_skipn.
  destruct ws eqn:Q. inversion H.
  simpl in *.  destruct (skipn n l). inversion H. inversion H0.
  exists w, w0, (firstn n l), (skipn (1+n) l).
  assert ( firstn n l ++ skipn n l = l) by apply firstn_skipn.
  split; [idtac | inversion H];
    do 3 f_equal;
    rewrite <- H1 in H2 at 2;
    apply app_inv_head, skipn_succ in H2;
    assumption.
Qed.

(* This is dependently-subtle... *)
Definition swap (n : nat) (ws : list word) (LEN : noflow ws) :=
   match firstn (1+n) ws, skipn (1+n) ws with
     | w0 :: l0, w1 :: l1 =>
          fun LEN2 => Some  {|
            stckval := (w1 :: l0) ++ w0 :: l1;
            stcksize := eq_ind_r inbounds LEN2 (swap_same_length w1 w0 l0 l1)
          |}
     | _, _ => fun _ => None
   end (eq_ind_r noflow LEN (firstn_skipn (1+n) ws)).

Definition exec_so_instr (i : so_instruction) (s : stack_t) : option stack_t :=
  match i, s with
    | I_STOP, _ => None
    | I_OP1 op, mkstack (w::st) LEN => Some (mkstack (eval_op1 op w::st) LEN)
    | I_OP1 _, mkstack nil _ => None
    | I_OP2 op, mkstack (w::w0::st) LEN => Some (mkstack (eval_op2 op w w0::st) (pop_lt LEN))
    | I_OP2 _, _ => None
    | I_OP3 op, mkstack (w::w0::w1::st) LEN => Some (mkstack (eval_op3 op w w0 w1::st) (pop_lt (pop_lt LEN)))
    | I_OP3 _, _ => None
    | I_POP, mkstack (w::st) LEN => Some (mkstack st (pop_lt LEN))
    | I_POP, _ => None
    | I_PUSH item, mkstack st _  => option_mkstack (item::st)
    | I_DUP n _, mkstack ws _  => dup n ws
    | I_SWAP n _, mkstack ws LEN => swap n ws LEN
  end.


Definition exec_jump_instr (i : instruction) (pc : nat) (s : stack_t) : option nat :=
  match i with
    | I_JUMP => match s with
                  | mkstack (to::xs) _ => Some to 
                  | _ => None
                end
    | I_JUMPI => match s with
                   | mkstack (to::cond::xs) _ => Some (if cond then to else pc + 1)
                   | _ => None
                end
    | I_STACK_ONLY (I_PUSH _) => Some (pc + 1) (* depends on code address encoding *)
    | _ => Some (pc + 1)
  end.

Theorem exec_so_nice : forall i st st',
  exec_so_instr i st = Some st' ->
    let d := delta (I_STACK_ONLY i) in
    let a := alpha (I_STACK_ONLY i) in
    stckval st' = firstn a (stckval st') ++ skipn d (stckval st).
Proof.
  destruct st as [s LEN]. simpl.
  destruct st' as [s' LEN']. simpl.
  intros.
  destruct (exec_so_instr i {| stckval := s; stcksize := LEN |}) eqn:Q; inversion H.
  subst s0. clear H.
  unfold exec_so_instr in Q.
  destruct i.
  + inversion Q.
  + destruct s; inversion Q. reflexivity.
  +
    destruct s eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    inversion Q.
    reflexivity.
  +
    destruct s eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    destruct l0; inversion Q.
    reflexivity.
  +
    destruct s eqn:?; inversion Q.
    reflexivity.
  +
    unfold option_mkstack in Q.
    destruct (le_lt_dec BOUND (length (w :: s))); inversion Q.
    reflexivity.
  + (* I_DUP *)
    unfold alpha, delta.
    unfold dup in Q; inversion Q.
    destruct (nth_error s n) eqn:NE; inversion Q.
    unfold option_mkstack in Q.
    destruct (le_lt_dec BOUND (length (w :: s))); inversion Q.
     simpl (snd (delta_alpha (I_STACK_ONLY (I_DUP n l)))).
     simpl (fst (delta_alpha (I_STACK_ONLY (I_DUP n l)))).
    assert (firstn_ssn : firstn (S (S n)) (w :: s) = w :: firstn (S n) s) by reflexivity.
    rewrite -> firstn_ssn.
    rewrite <- app_comm_cons.
    rewrite -> (firstn_skipn (S n) s).
    reflexivity.
  + (* I_SWAP *)
    unfold alpha, delta.
     simpl (snd (delta_alpha (I_STACK_ONLY (I_SWAP n l)))).
     simpl (fst (delta_alpha (I_STACK_ONLY (I_SWAP n l)))).
    rewrite <- (firstn_skipn (S (S n)) s') at 1.
    f_equal.
    unfold swap in Q.

Qed.

Require Import FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.
Definition memory := MapNat.t word.

Parameter mem_read_word : memory -> word -> word.
Parameter mem_store_word : memory -> word -> word -> memory.
Definition mem_store_byte (m: memory) (addr: word) (b: byte) : memory := add addr b m.

Definition first_byte (w: word) : byte := Nat.modulo w 32.

Definition exec_mem_instr (i : mem_instruction) (m : memory) (st : stack_t) : option (memory * stack_t) :=
  match i, st with
    | I_MLOAD, mkstack (addr::ws) LEN => Some (m, mkstack (mem_read_word m addr :: ws) LEN)
    | I_MSTORE, mkstack (addr::val::ws) _ => Some (mem_store_word m addr val, st)
    | I_MSTORE8, mkstack (addr::val::ws) _ => Some (mem_store_byte m addr (first_byte val), st)
    | _, _ => None
  end.

Definition storage := MapNat.t word.

Definition storage_read (p: storage) (addr: word) : word :=
  match find addr p with
    | Some v => v
    | None => 0
  end.
Definition storage_store (p: storage) (addr: word) (w: word) : memory :=
  add addr w p.

(* storage should be indexed by contract id *)
Definition exec_storage_instr (i : storage_instruction) (p : storage) (st : stack_t) : option (storage * stack_t) :=
  match i, st with
    | I_SLOAD, mkstack (addr::ws) LEN => Some (p, mkstack (storage_read p addr :: ws) LEN)
    | I_SSTORE, mkstack (addr::val::ws) _ => Some (storage_store p addr val, st)
    | _, _ => None
  end.

Variable size : nat.

Require Import Vector.
Variable code : Vector.t instruction size.




Record state := State {
  stack : stack_t;
  mem  : memory;
  stor : storage;
  pc : nat;
}.
