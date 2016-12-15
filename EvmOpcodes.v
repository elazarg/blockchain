(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)
Require Import Bool.
Require Import List.
Require Import Nat.
Require Import EqNat.
Require Import Arith.PeanoNat.


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
  | I_STACK_ONLY : so_instruction -> instruction
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



Definition word := nat.

(** The stack is represented as a Coq [list word]
    plus a proof that its lenth is smaller than 1024 *)
Record stack_t: Type := mkstack {
  stckval: list word; 
  stcksize: length stckval < 1024
}.

Lemma stack_pop_le {T: Type}: forall (c : T) cs (H : length (c::cs) < 1024),
  length cs < 1024.
Proof.
  intros.
  apply Lt.lt_S_n in H.
  apply Nat.lt_lt_succ_r.
  assumption.
Qed.

Definition pop (s : stack_t) : option stack_t :=
  match s with
    | mkstack (c::cs) p => Some (mkstack cs (stack_pop_le c cs p))
    | _ => None
  end.

Ltac consume H := 
  simpl;
  intros;
  repeat (assumption || apply Lt.lt_S_n in H; apply Nat.lt_lt_succ_r).

Lemma stack_app_le1 {T: Type}: forall (c : T) cs f (H : length (c::cs) < 1024),
  length ((f c)::cs) < 1024.
Proof.
  consume H.
Qed.

Lemma stack_app_le2 {T: Type}: forall (c1 c2 : T) cs f (H : length (c1::c2::cs) < 1024),
  length ((f c1 c2)::cs) < 1024.
Proof.
  consume H.
Qed.

Lemma stack_app_le3 {T: Type}: forall (c1 c2 c3: T) cs f (H : length (c1::c2::c3::cs) < 1024),
  length ((f c1 c2 c3)::cs) < 1024.
Proof.
  consume H.
Qed.

Definition apply_1_1 (f : word -> word) (s : stack_t) : option stack_t :=
  match s with
    | mkstack (c1::cs) p => Some (mkstack ((f c1)::cs) (stack_app_le1 c1 cs f p))
    | _ => None
  end.

Definition apply_2_1 (f : word -> word -> word) (s : stack_t) : option stack_t :=
  match s with
    | mkstack (c1::c2::cs) p => Some (mkstack ((f c1 c2)::cs)  (stack_app_le2 c1 c2 cs f p))
    | _ => None
  end.

Definition apply_3_1 (f : word -> word -> word -> word) (s : stack_t) : option stack_t :=
  match s with
    | mkstack (c1::c2::c3::cs) p => Some (mkstack ((f c1 c2 c3)::cs)  (stack_app_le3 c1 c2 c3 cs f p))
    | _ => None
  end.

Definition eval_op1 (op : op1) (c : word) : word :=
  match op with
    | OP_ISZERO => if c then 0 else 1
    | OP_NOT => if c then 0 else 1
  end.

Definition eval_op2 (op : op2) (c1 c2 : word) : word :=
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

Definition eval_op3 (op : op3) (c1 c2 c3 : word) : word :=
  match op with
    | OP_ADDMOD => c1
    | OP_MULMOD => c1
  end.
Require Import PeanoNat.

Require Import Arith.Compare_dec.


Definition push (xs : list word) :=
  if length xs <? 1024 then Some xs else None.

Theorem coerce (xs : list word) : {1024 <= length xs}+{length xs < 1024}.
Proof.
  apply le_lt_dec.
Defined.

Definition coerce' (xs : list word) : 
  {1024 <= length xs}
  +{exists (p:(length xs < 1024)) e, e = mkstack xs p}.
Proof.
  pose (coerce xs).
  inversion s. 
  - left. assumption.
  - right. exists H. exists ({| stckval := xs; stcksize := H |}).
    reflexivity.
Defined.

Lemma ltb_lt' {T: Type} : forall (e: T) n,
  (if n <? 1024 then Some e else None) = Some e -> n < 1024.
Proof.
  intros.
  pose (Nat.ltb_lt n 1024).
  inversion i; apply H0; clear i.
  destruct (n <? 1024). reflexivity. inversion H.
Qed.

Lemma p1 : forall xs, (exists xs', push xs = Some xs') <-> length xs < 1024.
Proof.
  intros. unfold push.
  split.
  - intro. apply (ltb_lt' xs).
    destruct (length xs <? 1024) eqn:Q. reflexivity. inversion H as [H1 H2]. inversion H2.
  - intros.
    exists xs.

      pose (Nat.ltb_lt (length xs) 1024). inversion i. clear i.
    destruct (length xs <? 1024). reflexivity. apply H1 in H. inversion H.
Qed.

Lemma p2 : forall xs st, push xs = Some st -> length st < 1024.
Proof.
  unfold push.
  intros.
  apply (ltb_lt' xs).
  destruct (length xs <? 1024) eqn:Q.
  - inversion H. rewrite -> H1 in *.
    rewrite -> Q. reflexivity.
  - inversion H.
Qed.

Lemma firstn_lt_1024 {T: Type}: forall (l: list T), length (firstn 1023 l) < 1024.
Proof.
  intros.
  apply Lt.le_lt_n_Sm.
  rewrite -> firstn_length.
  apply (Nat.le_min_l 1023 (length l)).
Qed.

Lemma qqq {T: Type}:
  forall (l: list T), length l <? 1024 = true -> length l < 1024.
Proof.
  intros.
  apply (Nat.ltb_lt (length l) 1024), H.
Qed.


Definition act (i : so_instruction) (s s' : stack_t) : Prop :=
  match i, stckval s, stckval s' with
   | I_STOP, _, _ => False
   | I_POP   , (_::cs)         , st' => st' = cs
   | I_POP   , _               , _   => False
   | I_OP1 op, (c1::cs)        , st' => st' = (eval_op1 op c1)::cs
   | I_OP1 _ , _               , _   => False
   | I_OP2 op, (c1::c2::cs)    , st' => st' = (eval_op2 op c1 c2)::cs
   | I_OP2 _ , _               , _   => False
   | I_OP3 op, (c1::c2::c3::cs), st' => st' = (eval_op3 op c1 c2 c3)::cs
   | I_OP3 _ , _               , _   => False
   | I_PUSH (x::xs), st, st' => st' = (x::xs) ++ st
   | I_PUSH _      , _ , _   => False
   | I_DUP (S n), st, (c0::st') =>
       st' = st
       /\ List.nth_error st (S n) = Some c0
   | I_DUP _, _, _ => False
   | I_SWAP (S n), (c::cs), (c'::cs') =>
       length (c::cs) > n
       /\ skipn n cs = skipn n cs'
       /\ firstn (n-1) cs = firstn (n-1) cs'
       /\ List.nth_error cs  n = Some c'
       /\ List.nth_error cs' n = Some c
   | I_SWAP _, _, _ => False
  end.

Definition exec_so_instr (i : so_instruction) (s : stack_t) : option stack_t :=
  match i with
    | I_STOP => None
    | I_OP1 op => apply_1_1 (eval_op1 op) s
    | I_OP2 op => apply_2_1 (eval_op2 op) s
    | I_OP3 op => apply_3_1 (eval_op3 op) s
    | I_POP => pop s
    | I_PUSH xs => let st' := xs ++ stckval s in
                   match Reflect length st' <? 1024 with
                     | ReflectT _ _ => Some (mkstack st' (qqq st'))
                     | false => None
                   end
    | _ => None
  end.
    | I_DUP n => match List.nth_error (stckval s) n with
                   | Some v => Some (mkstack (v::(stckval s)) (firstn_lt_1024 st'))
                   | None => None
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
    | I_STACK_ONLY (I_PUSH xs) => Some (pc + 1) (* depends on code address encoding *)
    | _ => Some (pc + 1)
  end.

Require Import Vector.
Require Import FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.
Definition byte := nat.
Definition memory := MapNat.t byte.
Definition storage := MapNat.t word.
Variable size : nat.
Variable code : Vector.t instruction size.




Record state := State {
  stack : stack_t;
  mem  : memory;
  stor : storage;
  pc : nat;
}.
