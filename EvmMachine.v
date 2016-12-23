(*
Sources:
"small ad-hoc symbolic interpreter" - https://gist.github.com/pirapira/0946d151e038393078c3
CompCert - https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v
*)
Require Import List.
Require Import ZArith.

Require Import Word.
Require Import Instructions.
Require Import Memory.
Require Import Stack.

Variable size : nat.

Require Import Vector.
Variable code : Vector.t instruction size.
Variable jump_targets : list nat.


Definition pc_t := Z.
Definition inc_pc (pc : pc_t) : pc_t := Z.add pc (1%Z).
Definition word_to_pc (w : word) : pc_t := Word.intval w.
Definition pc_to_word (pc : pc_t) : word := Word.repr pc.

Definition exec_jump_instr (i : instruction) (pc : pc_t) (ws : list word) : option (pc_t * list word) :=
  match i with
    | I_STOP => Some (pc, ws)
    | I_JUMP => match ws with
                  | (to::xs) => Some (word_to_pc to, xs)
                  | _ => None
                end
    | I_JUMPI => match ws with
                   | (to::cond::xs) => Some (if Word.eq cond Word.zero then (word_to_pc to) else (inc_pc pc), xs)
                   | _ => None
                end
    | I_STACK_ONLY (I_PUSH _) => Some (inc_pc pc, ws) (* depends on code address encoding *)
    | _ => Some (inc_pc pc, ws)
  end.


Record state := State {
  stack : list word;
  mem : memory;
  stor : storage;
  pc : Z;
}.

Definition step (i : instruction) st m p pc : option state :=
  let exec_so := fun i' => match exec_so_instr i' st with
                             | Some st' => Some (State st' m p pc)
                             | None => None
                           end in
  match i with
  | I_STACK_ONLY i' => exec_so i'

  | I_MEMINS i' => match exec_mem_instr i' m st with
                     | Some (m', st') => Some (State st' m' p pc)
                     | None => None
                   end
  | I_STORINS i' => match exec_storage_instr i' p st with
                     | Some (p', st') => Some (State st' m p' pc)
                     | None => None
                   end

  | I_STOP
  | I_JUMP
  | I_JUMPI => match exec_jump_instr i pc st with
                 | Some (pc', st') => Some (State st' m p pc')
                 | None => None
               end
  | I_PC => exec_so (I_PUSH (pc_to_word pc))
  | I_OTHER _ => None
  end.

Ltac dis_invert e Q := destruct e; inversion Q; try reflexivity.

Theorem step_nice : forall i st m p pc st' m' p' pc',
  step i st m p pc = Some (State st' m' p' pc') ->
    st' = firstn (alpha i) st' ++ skipn (delta i) st.
Proof.
  intros.
  destruct i; simpl in H; inversion H; simpl; try reflexivity.
  - apply exec_so_nice.
    dis_invert (exec_so_instr s st) H.
  - apply (exec_mem_nice _ m _ m' _).
    dis_invert (exec_mem_instr m0 m st) H.
    dis_invert p0 H.
  - apply (exec_storage_nice _ p _ p' _).
    dis_invert (exec_storage_instr s p st) H.
    dis_invert p0 H.
  - dis_invert st H.
  - dis_invert st H.
    dis_invert st H.
Qed.
