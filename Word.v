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

  Local Definition byte_at x i :=
    Z.shiftr (intval x) (32 - i) mod 256.

  Definition get_byte (left_index x : int) : int :=
    repr (byte_at x (intval left_index)).

  Definition sext (x y : int) : int :=
    sign_ext (intval x) y.

  Definition shl8 (w : int) := shl w (repr 8).

  Local Definition conc (w1 : int) (b : byte) :=
    repr ((unsigned (shl8 w1)) + (Byte.unsigned b)).

  Local Notation "a @ b" := (conc a b) (at level 1).

  Definition word_from_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : int :=
    zero @ b0 @ b1 @ b2 @ b3 @ b4 @ b5 @ b6 @ b7.

  Definition of_nat x := repr (Z.of_nat x).
  Definition bytes_from_word (w : int) : byte*byte*byte*byte*byte*byte*byte*byte :=
    let b := fun i => Byte.repr (byte_at w i) in
    (b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7).
End Word.

Definition word := Word.int.

Export Word.
