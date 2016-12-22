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

Module Word.
  Include Int256.

  Definition addmod (x y m : int) : int :=
    repr ((Z.add (unsigned x) (unsigned y)) mod (unsigned m)).

  Definition mulmod (x y m : int) : int :=
    repr ((Z.mul (unsigned x) (unsigned y)) mod (unsigned m)).

  Definition exp (x y : int) : int :=
    repr (Z.pow (unsigned x) (unsigned y)).

  Axiom least_byte : int -> int -> int.
  Axiom sext : int -> int -> int.

  Definition shl8 (w : int) := shl w (repr 8).

  Local Definition conc (w1 : int) (b : byte) :=  repr ((unsigned (shl8 w1)) + (Byte.unsigned b)).

  Local Notation "a @ b" := (conc a b) (at level 1).

  Definition word_from_bytes (a1 a2 a3 a4 a5 a6 a7 a8 : byte) : int :=
    zero @ a1 @ a2 @ a3 @ a4 @ a5 @ a6 @ a7 @ a8.

  Axiom bytes_from_word : int -> byte*byte*byte*byte*byte*byte*byte*byte.
End Word.

Definition word := Word.int.

Export Word.
