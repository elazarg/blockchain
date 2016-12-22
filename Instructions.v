
Require Import Integers.

Require Import NAxioms.
Require Import BinInt.

Definition word := int64.
Definition byte := byte.

Module Word := Int64.
Import Word.

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
    | OP_EXP => repr (Z.pow (unsigned x) (unsigned y))
    | OP_SIGNEXTEND => x (* sext c1 c2 *)
    | OP_LT => if lt x y then one else zero
    | OP_GT => if lt y x then one else zero
    | OP_SLT => negative (sub x y)
    | OP_SGT => negative (sub y x)
    | OP_EQ => if eq x y then one else zero
    | OP_AND => and x y
    | OP_OR => or x y
    | OP_XOR => xor x y
    | OP_BYTE => divu x y
  end.

Definition eval_op3 (op : op3) (x y m : word) : word :=
  match op with
    | OP_ADDMOD => repr ((Z.add (unsigned x) (unsigned y)) mod (unsigned m))
    | OP_MULMOD => repr ((Z.mul (unsigned x) (unsigned y)) mod (unsigned m))
  end.

Definition shl8 (w : word) :=  Word.shl w (repr 8).
Definition conc (w1 : word) (b : byte) :=  repr ((unsigned (shl8 w1)) + (Byte.unsigned b)).
Notation "a @ b" := (conc a b) (at level 1).

Definition word_from_bytes (a1 a2 a3 a4 a5 a6 a7 a8 : byte) : word :=
  zero @ a1 @ a2 @ a3 @ a4 @ a5 @ a6 @ a7 @ a8.

Axiom bytes_from_word : word -> byte*byte*byte*byte*byte*byte*byte*byte.
