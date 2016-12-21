(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)
Require Import Bool.
Require Import List.

Import ListNotations.

Require Import Nat.
Require Import EqNat.
Require Import Arith.
Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import PeanoNat.

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

Definition remove_option {T T' : Type} (f : T -> option T') x (P: f x <> None) : T' :=
  match f x as res return (res <> None -> T') with
    | Some t => fun _ => t
    | None => fun P0 => False_rect _ (P0 eq_refl)
  end P.

Lemma remove_option_sound : forall (T T' : Type) (f: T -> option T') x P,
  f x = Some (remove_option f x P).
Proof.
  intros.
  unfold remove_option.
  destruct (f x).
  + reflexivity.
  + contradiction.
Qed.

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

Lemma erased_swap_skipn : forall (w0 w1 : T) (l0 l1 : list T),
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

Lemma swap_long' : forall (n : nat) (ws : list T),
  1 + n < length ws ->
  swap n ws <> None.
Proof.
  unfold not.
  intros.
  unfold swap in H0.
  destruct (firstn (1 + n)) eqn:Q.
  - assert (L : 1 + n <= length ws) by (apply lt_le_S, Nat.lt_succ_l; assumption).
    apply firstn_length_le in L.
    rewrite -> Q in L.
    inversion L.
  - destruct (skipn (1 + n) ws) eqn:Q1.
    + apply lt_not_le in H.
      apply skipn_nil_length in Q1.
      contradiction.
    + inversion H0.
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

Lemma swap_alpha_2n_delta_2n : forall (n : nat) (ws ws' : list T),
  swap n ws = Some ws'
  -> skipn (2+n) ws = skipn (2+n) ws'.
Proof.
  intros.
  unfold swap in H.
  assert (FS: firstn (1+n) ws ++ skipn (1+n) ws = ws) by apply firstn_skipn.
  destruct (skipn (1 + n) ws) eqn:SKIP. inversion H.
  destruct (firstn (1 + n) ws). inversion H.
  assert (W: forall (w0: T) w1 l0 l1, ((w1 :: l0) ++ [w0]) ++ l1 = (w1 :: l0) ++ w0 :: l1). {
    intros. rewrite <- app_app. reflexivity.
  }
  rewrite <- W in H.
  inversion H.
  subst ws' ws.
  rewrite <- W.
  rewrite -> app_comm_cons at 1.
  rewrite <- app_comm_cons at 1.
  apply skipn_head_all in SKIP.
  assert (L2: length (t0 :: l0 ++ [t]) = (2 + n)). {
    rewrite -> app_comm_cons, app_length, plus_comm.
    inversion SKIP.
    reflexivity.
  }
  assert (R2: length (t :: l0 ++ [t0]) = (2 + n)). {
    rewrite -> app_comm_cons, app_length, plus_comm.
    inversion SKIP.
    reflexivity.
  }
  rewrite <- L2 at 1; rewrite -> skipn_short.
  rewrite <- R2 at 1; rewrite -> skipn_short.
  reflexivity.
Qed.

Definition swap_new (n : nat) (ws : list T) (E : 1+n < length ws) :=
  remove_option (swap n) ws (swap_long' n ws E).

End SWAP.

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

Definition exec_so_instr (i : so_instruction) (st : list word) : option (list word) :=
  match i, st with
    | I_STOP, _ => None
    | I_OP1 op, w::ws => Some (eval_op1 op w::ws)
    | I_OP1 _, nil => None
    | I_OP2 op, (w::w0::ws) => Some (eval_op2 op w w0::ws)
    | I_OP2 _, _ => None
    | I_OP3 op, (w::w0::w1::ws) => Some (eval_op3 op w w0 w1::ws)
    | I_OP3 _, _ => None
    | I_POP, (w::ws) => Some ws
    | I_POP, _ => None
    | I_PUSH item, ws  => Some (item::ws)
    | I_DUP n _, ws => match List.nth_error ws n with
                            | Some v => Some (v::ws)
                            | None => None
                          end
    | I_SWAP n _, ws => swap n ws
  end.

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
  + (* I_STOP *)
    discriminate Q.
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
    unfold exec_so_instr in Q.
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
