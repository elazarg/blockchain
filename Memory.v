Require Import ZArith.
Require Coqlib.

Require Import Instructions.
Require Import Integers.
Require Import Maps.
Require Import List.
Import ListNotations.

Definition memory := ZMap.t byte.
Definition mget (addr : word) (m : memory) : byte := (ZMap.get (Word.intval addr) m).

Definition mem_store_byte (addr : word) (b : byte) (m : memory) : memory :=
  (ZMap.set (Word.intval addr) b m).

Definition mem_store_first_byte (addr : word) (w : word) (m : memory) : memory :=
  (ZMap.set (Word.intval addr) (Byte.repr (Z.modulo (Word.intval w) 256)) m).

Definition mem_read_word (addr : word) (m : memory) : word :=
  let b := fun n => ZMap.get (Z.add (Word.intval addr) n) m in
  word_from_bytes (b 0%Z) (b 1%Z) (b 2%Z) (b 3%Z) (b 4%Z) (b 5%Z) (b 6%Z) (b 7%Z).

Definition mem_store_word (w : word) (addr : word) (m : memory) : memory :=
  let '(a0, a1, a2, a3, a4, a5, a6, a7) := bytes_from_word w in
  let s := fun '(n, b) (m' : memory) => ZMap.set (Z.add (Word.intval addr) (Z.of_nat n)) b m' in
  fold_right s m [(7, a7); (6, a6); (5, a5); (4, a4); (3, a3); (2, a2); (1, a1); (0, a0)].

Definition exec_mem_instr (i : mem_instruction) (m : memory) (ws : list word) : option (memory * list word) :=
  match i, ws with
    | I_MLOAD, addr::ws => Some (m, mem_read_word addr m :: ws )
    | I_MSTORE, addr::val::ws => Some (mem_store_word addr val m, ws)
    | I_MSTORE8, addr::val::ws => Some (mem_store_first_byte addr val m, ws)
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
Definition exec_storage_instr (i : storage_instruction) (p : storage) (ws : list word) : option (storage * list word) :=
  match i, ws with
    | I_SLOAD, addr::ws => Some (p, storage_read p addr :: ws)
    | I_SSTORE, addr::val::ws => Some (storage_store p addr val, ws)
    | _, _ => None
  end.

Variable size : nat.

Require Import Vector.
Variable code : Vector.t instruction size.

Record state := State {
  stack : list word;
  mem  : memory;
  stor : storage;
  pc : nat;
}.