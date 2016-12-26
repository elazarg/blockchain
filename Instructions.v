
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
  | I_OP1 : op1 -> so_instruction
  | I_OP2 : op2 -> so_instruction
  | I_OP3 : op3 -> so_instruction
  | I_POP
  | I_PUSH : nat -> so_instruction (* coerced from a list of 1-32 bytes, big endian; the rest is zero *)
  | I_DUP : nat -> so_instruction
  | I_SWAP : nat -> so_instruction
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

Inductive env_instruction : Type :=
  | I_ADDRESS | I_BALANCE | I_ORIGIN
  | I_CALLER | I_CALLVALUE | I_CALLDATALOAD | I_CALLDATASIZE | I_CALLDATACOPY
  | I_CODESIZE | I_CODECOPY | I_GASPRICE | I_EXTCODESIZE | I_EXTCODECOPY
.

Inductive block_instruction : Type :=
  | I_BLOCKHASH | I_COINBASE | I_TIMESTAMP | I_NUMBER | I_DIFFICULTY | I_GASLIMIT
.

Inductive system_instruction : Type :=
  | I_CREATE | I_CALL | I_CALLCODE | I_RETURN | I_DELEGATECALL | I_SUICIDE
.

Inductive other_instruction : Type :=
  | I_SHA3
  | I_MSIZE | I_GAS | I_JUMPDEST (* NO-OP - mark as label *)
  | I_LOG : nat (* 0-4 *) -> other_instruction
.

Inductive instruction : Type :=
  | I_STOP
  | I_STACK : so_instruction -> instruction
  | I_MEMINS : mem_instruction -> instruction
  | I_STORINS : storage_instruction -> instruction

  | I_JUMP
  | I_JUMPI
  | I_PC

  | I_ENV : env_instruction -> instruction
  | I_BLOCK : block_instruction -> instruction
  | I_SYS : system_instruction -> instruction
  | I_OTHER : other_instruction -> instruction
  | I_INVALID : instruction
.


Definition delta_alpha (i: instruction) : nat*nat :=
  match i with
    | I_STOP => (0, 0)
    | I_STACK (I_OP1 _) => (1, 1)
    | I_STACK (I_OP2 _) => (2, 1)
    | I_STACK (I_OP3 _) => (3, 1)
    | I_STACK I_POP => (1, 0)
    | I_STACK (I_PUSH n) => (0, 1)
    | I_STACK (I_DUP n) => (n, 1 + n)
    | I_STACK (I_SWAP n) => (2 + n, 2 + n)
    | I_OTHER I_SHA3 => (2, 1)

    | I_ENV I_ADDRESS => (0, 1)
    | I_ENV I_BALANCE => (1, 1)
    | I_ENV I_ORIGIN => (0, 1)
    | I_ENV I_CALLER => (0, 1)
    | I_ENV I_CALLVALUE => (0, 1)
    | I_ENV I_CALLDATALOAD => (1, 1)
    | I_ENV I_CALLDATASIZE => (0, 1)
    | I_ENV I_CALLDATACOPY => (3, 0)
    | I_ENV I_CODESIZE => (0, 1)
    | I_ENV I_CODECOPY => (3, 0)
    | I_ENV I_GASPRICE => (0, 1)
    | I_ENV I_EXTCODESIZE => (1, 1)
    | I_ENV I_EXTCODECOPY => (4, 0)

    | I_BLOCK I_BLOCKHASH => (1, 1)
    | I_BLOCK I_COINBASE => (0, 1)
    | I_BLOCK I_TIMESTAMP => (0, 1)
    | I_BLOCK I_NUMBER => (0, 1)
    | I_BLOCK I_DIFFICULTY => (0, 1)
    | I_BLOCK I_GASLIMIT => (0, 1)

    | I_MEMINS I_MLOAD => (1, 1)
    | I_MEMINS I_MSTORE => (2, 0)
    | I_MEMINS I_MSTORE8 => (2, 0)
    | I_STORINS I_SLOAD => (1, 1)
    | I_STORINS I_SSTORE => (2, 0)

    | I_JUMP => (1, 0)
    | I_JUMPI => (2, 0)
    | I_PC => (0, 1)

    | I_OTHER I_MSIZE => (0, 1)
    | I_OTHER I_GAS => (0, 1)
    | I_OTHER I_JUMPDEST  => (0, 0) (* NO-OP - mark as label *)

    | I_OTHER (I_LOG n) => (n + 2, 0)

    | I_SYS I_CREATE => (3, 1)
    | I_SYS I_CALL => (7, 1)
    | I_SYS I_CALLCODE => (7, 1)
    | I_SYS I_RETURN => (2, 0)
    | I_SYS I_DELEGATECALL => (6, 1)
    | I_INVALID => (0, 0)
    | I_SYS I_SUICIDE => (1, 10)
  end.

Require Import List PeanoNat.
Import ListNotations.

Local Definition fill16 (l : list instruction) : list instruction:=
  l ++ repeat I_INVALID (16 - length l).

(* 0s: Stop and Arithmetic Operations *)
Definition opcode_0s := fill16 [
 I_STOP;

 I_STACK (I_OP2 OP_ADD);
 I_STACK (I_OP2 OP_MUL);
 I_STACK (I_OP2 OP_SUB);
 I_STACK (I_OP2 OP_DIV);
 I_STACK (I_OP2 OP_SDIV);
 I_STACK (I_OP2 OP_MOD);
 I_STACK (I_OP2 OP_SMOD);
 I_STACK (I_OP3 OP_ADDMOD);
 I_STACK (I_OP3 OP_MULMOD);
 I_STACK (I_OP2 OP_EXP);
 I_STACK (I_OP2 OP_SIGNEXTEND)
].

(* 10s: Comparison & Bitwise Logic Operations *)
Definition opcode_10s := fill16 [
 I_STACK (I_OP2 OP_LT);
 I_STACK (I_OP2 OP_GT);
 I_STACK (I_OP2 OP_SLT);
 I_STACK (I_OP2 OP_SGT);
 I_STACK (I_OP2 OP_EQ);
 I_STACK (I_OP1 OP_ISZERO);
 I_STACK (I_OP2 OP_AND);
 I_STACK (I_OP2 OP_OR);
 I_STACK (I_OP2 OP_XOR);
 I_STACK (I_OP1 OP_NOT);
 I_STACK (I_OP2 OP_BYTE)
].

(* 20s: SHA3 *)
Definition opcode_20s := fill16 [
  I_OTHER I_SHA3
].

(* 30s: Environmental Information *)
Definition opcode_30s := fill16 [
 I_ENV I_ADDRESS;
 I_ENV I_BALANCE;
 I_ENV I_ORIGIN;
 I_ENV I_CALLER;
 I_ENV I_CALLVALUE;
 I_ENV I_CALLDATALOAD;
 I_ENV I_CALLDATASIZE;
 I_ENV I_CALLDATACOPY;
 I_ENV I_CODESIZE;
 I_ENV I_CODECOPY;
 I_ENV I_GASPRICE;
 I_ENV I_EXTCODESIZE;
 I_ENV I_EXTCODECOPY
].

(* 50s: Stack, Memory, Storage and Flow Operations *)
Definition opcode_40s := fill16 [
 I_BLOCK I_BLOCKHASH;
 I_BLOCK I_COINBASE;
 I_BLOCK I_TIMESTAMP;
 I_BLOCK I_NUMBER;
 I_BLOCK I_DIFFICULTY;
 I_BLOCK I_GASLIMIT
].

(* 50s: Stack, Memory, Storage and Flow Operations *)
Definition opcode_50s := fill16 [
 I_STACK I_POP;
 I_MEMINS I_MLOAD;
 I_MEMINS I_MSTORE;
 I_MEMINS I_MSTORE8;
 I_STORINS I_SLOAD;
 I_STORINS I_SSTORE;
 I_JUMP;
 I_JUMPI;
 I_PC;
 I_OTHER I_MSIZE;
 I_OTHER I_GAS;
 I_OTHER I_JUMPDEST
].

(* f0s: System operations *)
Definition opcode_f0s := [
 I_SYS I_CREATE;
 I_SYS I_CALL;
 I_SYS I_CALLCODE;
 I_SYS I_RETURN;
 I_SYS I_DELEGATECALL
] ++ repeat I_INVALID 10 ++ [
 I_SYS I_SUICIDE
].


Definition opcode : list instruction := []
(* 0 *) ++ opcode_0s
(* 1 *) ++ opcode_10s
(* 2 *) ++ opcode_20s
(* 3 *) ++ opcode_30s
(* 4 *) ++ opcode_40s
(* 5 *) ++ opcode_50s
(* 6 *) ++ map (fun n => I_STACK (I_PUSH n)) (seq 1 16)
(* 7 *) ++ map (fun n => I_STACK (I_PUSH n)) (seq 17 16)
(* 8 *) ++ map (fun n => I_STACK (I_DUP n)) (seq 1 16)
(* 9 *) ++ map (fun n => I_STACK (I_SWAP n)) (seq 1 16)
(* a *) ++ fill16 (map (fun n => I_OTHER (I_LOG n)) (seq 0 5))
(* b *) ++ fill16 []
(* c *) ++ fill16 []
(* d *) ++ fill16 []
(* e *) ++ fill16 []
(* f *) ++ opcode_f0s
.

Definition delta (i: instruction) := fst (delta_alpha i).
Definition alpha (i: instruction) := snd (delta_alpha i).

Require Export Word.
Include Word.Word.

Definition eval_op1 (op : op1) (x : word) : word :=
  match op with
    | OP_ISZERO => if eq x zero then one else zero
    | OP_NOT => neg x
  end.

Definition eval_op2 (op : op2) (x y : word) : word :=
  match op with
    | OP_ADD => add x y
    | OP_MUL => mul x y
    | OP_SUB => sub x y
    | OP_DIV => divu x y
    | OP_SDIV => divs x y
    | OP_MOD => modu x y
    | OP_SMOD => mods x y
    | OP_EXP => exp x y
    | OP_SIGNEXTEND => sext x y
    | OP_LT => if lt x y then one else zero
    | OP_GT => if lt y x then one else zero
    | OP_SLT => negative (sub x y)
    | OP_SGT => negative (sub y x)
    | OP_EQ => if eq x y then one else zero
    | OP_AND => and x y
    | OP_OR => or x y
    | OP_XOR => xor x y
    | OP_BYTE => get_byte x y
  end.

Definition eval_op3 (op : op3) (x y m : word) : word :=
  match op with
    | OP_ADDMOD => addmod x y m
    | OP_MULMOD => mulmod x y m
  end.
