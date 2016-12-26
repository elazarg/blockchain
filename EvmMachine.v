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


Definition exec_mem_instr (i : mem_instruction) (m : memory) (ws : list word) : option (memory * list word) :=
  match i, ws with
    | I_MLOAD, addr::ws => Some (m, mem_read_word addr m :: ws )
    | I_MSTORE, addr::val::ws => Some (mem_store_word addr val m, ws)
    | I_MSTORE8, addr::val::ws => Some (mem_store_first_byte addr val m, ws)
    | _, _ => None
  end.

(* storage should be indexed by contract id *)
(* TODO: this is remarkably similar to the interface of CompCerts' Memory.v *)
Definition exec_storage_instr (i : storage_instruction) (p : storage) (ws : list word) : option (storage * list word) :=
  match i, ws with
    | I_SLOAD, addr::ws => Some (p, storage_read addr p :: ws)
    | I_SSTORE, addr::val::ws => Some (storage_store addr val p, ws)
    | _, _ => None
  end.
Variable c : code.
Record state := State {
  stack : list word;
  mem : memory;
  stor : storage;
  pc : pc_t;
}.

Definition step (i : instruction) st m p pc : option state :=
  let mks := fun ost' => match ost' with
                           | Some st' => Some (State st' m p pc)
                           | None => None
                         end in
  match i with
    | I_STACK (I_OP1 op) => mks (apply_1 (eval_op1 op) st)
    | I_STACK (I_OP2 op) => mks (apply_2 (eval_op2 op) st)
    | I_STACK (I_OP3 op) => mks (apply_3 (eval_op3 op) st)
    | I_STACK I_POP => mks (Some (tl st))
    | I_STACK (I_PUSH  n) => mks (Some (code_read_word_from_n_bytes pc n c::st))
    | I_STACK (I_DUP n) => mks (dup n st)
    | I_STACK (I_SWAP n) => mks (swap n st)

    | I_MEMINS i' => match exec_mem_instr i' m st with
                     | Some (m', st') => Some (State st' m' p (inc_pc pc))
                     | None => None
                   end
    | I_STORINS i' => match exec_storage_instr i' p st with
                     | Some (p', st') => Some (State st' m p' (inc_pc pc))
                     | None => None
                   end

    | I_STOP => Some (State st m p pc)
    | I_JUMP => match st with
                  | (to::st') => Some (State st' m p to)
                  | _ => None
                end
    | I_JUMPI => match st with
                   | (to::cond::st') => let pc' := if Word.eq cond Word.zero 
                                                   then (inc_pc pc)
                                                   else to
                                        in Some (State st' m p pc')
                   | _ => None
                end
    | I_PC => mks (Some (pc::st))
    | I_BLOCK _ => None

    | I_ENV I_ADDRESS => None
    | I_ENV I_BALANCE => None
    | I_ENV I_ORIGIN => None
    | I_ENV I_CALLER => None
    | I_ENV I_CALLVALUE => None
    | I_ENV I_CALLDATALOAD => None
    | I_ENV I_CALLDATASIZE => None
    | I_ENV I_CALLDATACOPY => None
    | I_ENV I_CODESIZE => None
    | I_ENV I_CODECOPY => match st with
                            | to::from::count::st' => Some (State st' (copy_code_to_memory c m to from count) p pc)
                            | _ => None
                          end
    | I_ENV I_GASPRICE => None
    | I_ENV I_EXTCODESIZE => None
    | I_ENV I_EXTCODECOPY => None

    | I_SYS _ => None
    | I_OTHER _ => None
    | I_INVALID => None
  end.

(* 
Lemma exec_mem_nice : forall i m st m' st',
  exec_mem_instr i m st = Some (m', st') ->
    st' = firstn (alpha (I_MEMINS i)) st' ++ skipn (delta (I_MEMINS i)) st.
Proof.
  intros.
  destruct (exec_mem_instr i m st) eqn:Q; inversion H.
  subst.
  destruct i; repeat (destruct st; inversion Q; try reflexivity).
Qed.


Lemma exec_storage_nice : forall i p st p' st',
  exec_storage_instr i p st = Some (p', st') ->
    st' = firstn (alpha (I_STORINS i)) st' ++ skipn (delta (I_STORINS i)) st.
Proof.
  intros.
  destruct (exec_storage_instr i p st) eqn:Q; inversion H.
  subst.
  destruct i; repeat (destruct st; inversion Q; try reflexivity).
Qed.

Lemma exec_so_nice : forall i st st' m p pc,
  (step (I_STACK i) st m p pc) = Some (State st' m p pc) ->
    let a := (alpha (I_STACK i)) in
    let d := (delta (I_STACK i)) in
    st' = firstn a st' ++ skipn d st.
Proof.
  intros.
  destruct (step (I_STACK i) st m p pc0) eqn:Q; inversion H.
  subst s.
  destruct i.
  + (* I_OP1 *)
    destruct st; inversion Q.
    reflexivity.
  + (* I_OP2 *)
    destruct st eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    inversion Q.
    reflexivity.
  + (* I_OP3 *)
    destruct st eqn:?. simplify_eq Q.
    destruct l eqn:?. simplify_eq Q.
    destruct l0; inversion Q.
    reflexivity.
  + (* I_POP *)
    simpl in Q. unfold tl in Q.
    destruct st eqn:?; inversion Q; reflexivity.
  + (* I_PUSH *)
    inversion Q.
    reflexivity.
  + (* I_DUP *)
    unfold step in Q. unfold dup in Q.
    destruct (nth_error st n) eqn:NE; inversion Q.
    destruct st. destruct n; inversion NE.
    simpl. f_equal. f_equal.
    symmetry.
    apply firstn_skipn.
  + (* I_SWAP *)
    simpl in Q.
    compute in a. subst a.
    compute in d. subst d.
    destruct (swap n st) eqn:Q1; inversion Q.
    apply swap_alpha_2n_delta_2n in Q1. inversion Q. subst l.
    rewrite <- (firstn_skipn (S (S n)) st') at 1.
    symmetry.
    apply f_equal.
    assumption.
Qed.

Ltac dis_invert e Q := destruct e; inversion Q; try reflexivity.

Theorem step_nice : forall i st m p pc st' m' p' pc',
  step i st m p pc = Some (State st' m' p' pc') ->
    st' = firstn (alpha i) st' ++ skipn (delta i) st.
Proof.
  intros.
  destruct i; simpl in H; inversion H; simpl; try reflexivity.
  - simpl in H1.
    unfold delta, alpha.
    destruct s. simpl. H. in
    apply (exe_so_nice s st st' m' p' pc').
    destruct (step (I_STACK s) st m' p' pc').
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
*)