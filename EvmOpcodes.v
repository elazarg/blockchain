(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)

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
  | I_PUSH : list nat (* length 1-32 *) -> so_instruction
  | I_DUP : nat (* 1-16 *) -> so_instruction
  | I_SWAP : nat (* 1-16 *) -> so_instruction
.

Inductive instruction : Type :=
  | STACK_ONLY : so_instruction -> instruction
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

Require Import Bool List Nat EqNat.

Require Import Vector.
Require Import Arith.PeanoNat.
Require Import FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.

Definition cell := nat.
Definition memory := MapNat.t nat.
Definition stack_t := list cell.

Variable size : nat.
Variable code : Vector.t instruction size.

Record state := State {
  stack : stack_t;
  mem  : memory;
  pers : memory;
  pc : nat;
}.


Definition apply_1_1 (f : cell -> cell) (s : stack_t) : option stack_t :=
  match s with
    | c1::cs => Some ((f c1)::cs)
    | _ => None
  end.

Definition apply_2_1 (f : cell -> cell -> cell) (s : stack_t) : option stack_t :=
  match s with
    | c1::c2::cs => Some ((f c1 c2)::cs)
    | _ => None
  end.

Definition apply_3_1 (f : cell -> cell -> cell -> cell) (s : stack_t) : option stack_t :=
  match s with
    | c1::c2::c3::cs => Some ((f c1 c2 c3)::cs)
    | _ => None
  end.

Definition exec_op1 (op : op1) (c : cell) : cell :=
  match op with
    | OP_ISZERO => if c then 0 else 1
    | OP_NOT => if c then 0 else 1
  end.

Definition exec_op2 (op : op2) (c1 c2 : cell) : cell :=
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

Definition exec_op3 (op : op3) (c1 c2 c3 : cell) : cell :=
  match op with
    | OP_ADDMOD => c1
    | OP_MULMOD => c1
  end.

Definition exec_so_instr (i : so_instruction) (s : stack_t) : option stack_t :=
  match i with
    | I_STOP => None
    | I_OP1 op => apply_1_1 (exec_op1 op) s
    | I_OP2 op => apply_2_1 (exec_op2 op) s
    | I_OP3 op => apply_3_1 (exec_op3 op) s
    | I_POP => if s then Some (List.tl s) else None
    | I_PUSH xs => Some (xs ++ s)
    | I_DUP n => match List.nth_error s n with
                   | None => None
                   | Some v => Some (v::s)
                  end
    | I_SWAP n => let depth := firstn n s in
                  if ltb (length depth) n then None else Some (depth ++ s)
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
    | _ => Some (pc + 1)
  end.