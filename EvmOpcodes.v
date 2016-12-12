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
  | OP_SIGNEXTEND (* 2 *)
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

Inductive instruction : Type :=
  | I_STOP
  | I_OP1 : op1 -> instruction
  | I_OP2 : op2 -> instruction
  | I_OP3 : op3 -> instruction
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

  | I_POP
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
  | I_JUMPDEST

  | I_PUSH : nat (* 1-32 *) -> instruction
  | I_DUP : nat (* 1-16 *) -> instruction
  | I_SWAP : nat (* 1-16 *) -> instruction
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
Definition code := Vector.t instruction.
Definition stack := list cell.

Record state := State {
  st : stack;
  mem  : memory;
  pers : memory;
  pc : nat;
}.

Definition set_stack (s : state) (st' : stack) : state :=
  State st' (mem s) (pers s) (pc s).

Definition set_pc (s : state) (pc' : nat) : state :=
  State (st s) (mem s) (pers s) pc'.

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


Definition exec_instr (i : instruction) (s : state) : option state  :=
  match i, s with
  | I_STOP, _ => None
  | I_OP1 op, {| st:=(x::xs) |} => Some (set_stack s ((exec_op1 op x)::xs))
  | I_OP2 op, {| st:=(x::y::xs) |} => Some (set_stack s ((exec_op2 op x y)::xs))
  | I_OP3 op, {| st:=(x::y::z::xs) |} => Some (set_stack s ((exec_op3 op x y z)::xs))
  | I_POP,    {| st:=(x::xs) |} => Some (set_stack s xs)
  | _, _ => None
  end.
