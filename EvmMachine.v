

Variable size : nat.

Require Import Vector.
Variable code : Vector.t instruction size.

Record state := State {
  stack : list word;
  mem  : memory;
  stor : storage;
  pc : nat;
}.
