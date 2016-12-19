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
  | I_PUSH (items : list nat) : (0 < length items /\ length items <= 32) -> so_instruction
  | I_DUP (n : nat) : n < 16 -> so_instruction (* n is one less than DUPN *)
  | I_SWAP (n : nat) : n < 16 -> so_instruction (* n is one less than SWAPN *)
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

  | I_MLOAD
  | I_MSTORE
  | I_MSTORE8
  | I_SLOAD
  | I_SSTORE

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



Definition word := nat.

(** The stack is represented as a Coq [list word]
    plus a proof that its lenth is smaller than 1024 *)
Record stack_t: Type := mkstack {
  stckval: list word; 
  stcksize: length stckval < 1024
}.

Lemma pop_lt : forall {w : word} {ws: list word}, length (w :: ws) < 1024 -> length ws < 1024.
Proof.
  intros.
  exact (Nat.lt_lt_succ_r (length ws) 1023 (lt_S_n (length ws) 1023 H)).
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


Definition option_mkstack (st : list word) : option stack_t :=
  match le_lt_dec 1024 (length st) with
    | right LEN => Some (mkstack st LEN)
    | left _ => None
  end.

Lemma swap_same_length : forall T (w0 w1 : T) l0 l1,
  length ((w0 :: l0) ++ w1 :: l1) = length ((w1 :: l0) ++ w0 :: l1).
Proof.
  intros.
  rewrite -> app_length.
  rewrite -> app_length.
  reflexivity.
Qed.

Definition inbounds n : Prop := n < 1024.
Definition noflow (xs : list word) : Prop := inbounds (length xs).

Definition exec_so_instr' (i : so_instruction) (s : stack_t) : option stack_t :=
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
    | I_PUSH items _, mkstack st _  => option_mkstack (items ++ st)
    | I_DUP n _, mkstack st _  =>
             match List.nth_error st n with
               | Some v => option_mkstack (v::st)
               | None => None
             end
    | I_SWAP n _, mkstack ws LEN =>
             let LEN_FS := eq_ind_r noflow LEN (firstn_skipn n ws) in
             match firstn n ws, skipn n ws with
               | w0::l0, w1::l1 => fun LEN2 => Some {|
                                      stckval := (w1 :: l0) ++ w0 :: l1;
                                      stcksize := eq_ind_r inbounds LEN2
                                                    (swap_same_length word w1 w0 l0 l1)
                                   |}
               | _, _ => fun _ => None
             end LEN_FS
  end.

Definition exec_jump_instr (i : instruction) (pc : nat) (s : stack_t) : option nat :=
  match i with
    | I_JUMP => match s with
                  | to::xs => Some to 
                  | _ => None
                end
    | I_JUMPI => match s with
                   | to::cond::xs => Some (if cond then to else pc + 1)
                   | _ => None
                end
    | I_STACK_ONLY (I_PUSH xs) => Some (pc + 1) (* depends on code address encoding *)
    | _ => Some (pc + 1)
  end.

Require Import Vector.
Require Import FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.
Definition byte := nat.
Definition memory := MapNat.t byte.
Definition storage := MapNat.t word.
Variable size : nat.
Variable code : Vector.t instruction size.




Record state := State {
  stack : stack_t;
  mem  : memory;
  stor : storage;
  pc : nat;
}.
