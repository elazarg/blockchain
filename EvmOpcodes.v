(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)
Require Import Bool.
Require Import List.
Require Import Nat.
Require Import EqNat.
Require Import Arith.
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
  | I_PUSH (items : list nat) : (0 < length items /\ length items <= 32) -> so_instruction
  | I_DUP (n : nat) : n < 16 -> so_instruction (* n is one less than DUPN *)
  | I_SWAP1 : so_instruction
  | I_SWAP2 : so_instruction
  | I_SWAP3 : so_instruction
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

Definition pop' (w : word) (ws : list word) (H : length (w :: ws) < 1024) : stack_t :=
 {|
   stckval := ws;
   stcksize := Nat.lt_lt_succ_r (length ws) 1023 (lt_S_n (length ws) 1023 H)
 |}.

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
   | I_PUSH cs P, st, st' => st' = cs ++ st
   | I_DUP n P, st, (c0::st') =>
       st' = st
       /\ List.nth_error st n = Some c0
   | I_DUP _ _, _, _ => False
   | I_SWAP1, (x::y::cs), (y'::x'::cs') =>
       x = x' /\ y = y' /\ cs = cs'
   | I_SWAP1, _, _ => False
   | I_SWAP2, (x::c1::y::cs), (y'::c1'::x'::cs') =>
       x = x' /\ y = y' /\ cs = cs' /\ c1 = c1'
   | I_SWAP2, _, _ => False
   | I_SWAP3, (x::c1::c2::y::cs), (y'::c1'::c2'::x'::cs') =>
       x = x' /\ y = y' /\ cs = cs' /\ c1 = c1' /\ c2 = c2'
   | I_SWAP3, _, _ => False
  end.


Lemma t : forall i s, (forall s', ~ act i s s')\/(exists s', act i s s').
Proof.
  intros.
  destruct s.
  destruct i; auto.
  - destruct stckval0; auto.
    simpl. right.
    exists (mkstack ((eval_op1 o w)::stckval0) (stack_app_le1 w stckval0 (eval_op1 o) stcksize0)).
    reflexivity.
  - destruct stckval0; auto.
    destruct stckval0; auto.
    simpl. right.
    exists (mkstack ((eval_op2 o w w0)::stckval0) (stack_app_le2 w w0 stckval0 (eval_op2 o) stcksize0)).
    reflexivity.
  - destruct stckval0; auto.
    destruct stckval0; auto.
    destruct stckval0; auto.
    simpl. right.
    exists (mkstack ((eval_op3 o w w0 w1)::stckval0) (stack_app_le3 w w0 w1 stckval0 (eval_op3 o) stcksize0)).
    reflexivity.
  - destruct stckval0; auto.
    right. simpl. exists (pop' w stckval0 stcksize0).
    reflexivity.
  - simpl.
    clear stcksize0.
    pose (le_lt_dec 1024 (length (items ++ stckval0))).
    inversion s.
    + clear s. left. intros. destruct s'. simpl.
      intro. rewrite <- H0 in *. clear a H0 stckval0 items.
      apply (le_not_lt 1024 (length stckval1) H).
      assumption.
    + clear s. right.
      exists (mkstack (items ++ stckval0) H).
      reflexivity.
  - simpl.
    clear stcksize0.
    pose (le_lt_dec (length stckval0) n).
    inversion s.
    + left. intros [cs P]. simpl. destruct cs; auto.
      intro. inversion H0 as [_ N]. 
      assert (nth_error stckval0 n <> None). intro. rewrite -> H1 in N.  inversion N.
      apply nth_error_Some in H1.
      apply (le_not_lt (length stckval0) n). assumption. assumption.
    + pose (le_lt_dec 1023 (length stckval0)).
      inversion s0.
      * left.
        intro. destruct s'. destruct stckval1; auto. simpl.
        intros [A B]. rewrite -> A in stcksize0.
        simpl in stcksize0.
        apply (le_not_lt 1023 (length stckval0)); auto. 
          apply Lt.lt_S_n.
        assumption.
     * right. clear s.
       pose (nth_error stckval0 n).
       assert (forall w, length (w::stckval0) < 1024) by (intros; simpl; apply Lt.lt_n_S; assumption).
       destruct (nth_error stckval0 n) eqn:Q.
       ** assert (length (w::stckval0) < 1024) by (simpl; apply Lt.lt_n_S; assumption).
          exists (mkstack (w::stckval0) (H1 w)).
          simpl. auto.
       ** apply nth_error_None in Q.
          apply (le_not_lt (length stckval0) n Q) in H. inversion H.
  - destruct stckval0. left; auto.
    destruct stckval0. simpl; auto.
    right. simpl. 
    exists (mkstack (w0 :: w :: stckval0) stcksize0); simpl;  auto.
  - destruct stckval0. left; auto.
    destruct stckval0. simpl; auto.
    destruct stckval0. simpl; auto.
    right. simpl. 
    exists (mkstack (w1 :: w0 :: w :: stckval0) stcksize0); simpl;  auto.
  - destruct stckval0. left; auto.
    destruct stckval0. simpl; auto.
    destruct stckval0. simpl; auto.
    destruct stckval0. simpl; auto.
    right. simpl. 
    exists (mkstack (w2 :: w0 :: w1 :: w :: stckval0) stcksize0); simpl;  auto.
Defined.


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
