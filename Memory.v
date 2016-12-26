Require Import List.
Require Import ZArith.

Require Coqlib.
Require Import Integers.
Require Import Maps.

Require Import Word.

Import ListNotations.

Module WordMap := ZMap.

Section Memory.

Definition memory := WordMap.t byte.
Definition mem_read_byte (addr : word) (m : memory) : byte := (WordMap.get (Word.intval addr) m).

Definition mem_store_byte (addr : word) (b : byte) (m : memory) : memory :=
  (ZMap.set (Word.intval addr) b m).

Definition mem_store_first_byte (addr : word) (w : word) (m : memory) : memory :=
  (ZMap.set (Word.intval addr) (Byte.repr (Z.modulo (Word.intval w) 256)) m).

Definition mem_read_word_from_n_bytes (addr: word) (n: nat) (m : memory) : word :=
  Word.word_from_byte_seq (map (fun i => mem_read_byte (add (Word.of_nat i) addr) m) (seq 0 n)).

Definition mem_read_word (addr : word) (m : memory) : word :=
  let b := fun n => WordMap.get (Z.add (Word.intval addr) n) m in
  word_from_bytes (b 0%Z) (b 1%Z) (b 2%Z) (b 3%Z) (b 4%Z) (b 5%Z) (b 6%Z) (b 7%Z).

Local Definition wordadd addr n :=
  Word.repr (Z.add (Word.intval addr) (Z.of_nat n)).

Definition mem_store_word (w : word) (addr : word) (m : memory) : memory :=
  let '(a0, a1, a2, a3, a4, a5, a6, a7) := bytes_from_word w in
  let s := fun '(n, b) (m' : memory) => mem_store_byte (wordadd addr n) b m' in
  fold_right s m [(7, a7); (6, a6); (5, a5); (4, a4); (3, a3); (2, a2); (1, a1); (0, a0)].


End Memory.

Section Storage.

Definition storage := WordMap.t word.

Definition storage_read (addr: word) (p: storage) : word := WordMap.get (Word.intval addr) p.

Definition storage_store (addr: word) (w: word) (p: storage) : storage := WordMap.set (Word.intval addr) w p.


End Storage.


Require Import Instructions.
Require Import ZArith.Znat.

Section Code.

Definition code := memory.


Definition pc_t := word.
Definition inc_pc (pc : pc_t) : pc_t := add pc one.

Definition code_read_byte := mem_read_byte.
Definition code_read_word_from_n_bytes := mem_read_word_from_n_bytes.

Definition code_read_instruction (pc: pc_t) (c: code) : instruction :=
  nth (Z.to_nat (Byte.unsigned (code_read_byte pc c))) opcode I_INVALID.

Local Definition addrseq (addr count : word) : list word :=
  map (wordadd addr) (seq 0 (Z.to_nat (Word.unsigned count))).

Definition copy_code_to_memory (c: code) (m: memory) (to from count : word) : memory :=
  fold_right (fun '(t, f) m' => mem_store_byte t (code_read_byte f m) m') m (combine (addrseq from count) (addrseq to count)).


End Code.
