Require Import Coqlib.
Require Import Integers.

Definition byte := byte.

Module Wordsize_256.
  Definition wordsize := 256%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_256.

Strategy opaque [Wordsize_256.wordsize].

Module Int256.

Include Make(Wordsize_256).
End Int256.

Notation int256 := Int256.int.

Module Word := Int256.
Definition word := Word.int.

Import Word.

Definition shl8 (w : word) := shl w (repr 8).

Definition conc (w1 : word) (b : byte) :=  repr ((unsigned (shl8 w1)) + (Byte.unsigned b)).

Notation "a @ b" := (conc a b) (at level 1).

Definition word_from_bytes (a1 a2 a3 a4 a5 a6 a7 a8 : byte) : word :=
  zero @ a1 @ a2 @ a3 @ a4 @ a5 @ a6 @ a7 @ a8.

Axiom bytes_from_word : word -> byte*byte*byte*byte*byte*byte*byte*byte.
