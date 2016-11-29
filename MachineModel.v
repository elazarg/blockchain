Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Arith.PeanoNat.
Require Import Relations.Relation_Definitions.

Require Import FSets.FSetWeakList.

Module Import Collection := FSetWeakList.Make Nat.

Section MachineDef.

Definition TransactionRequest := nat.

Parameter PersistentState : Type.

Parameter startState : PersistentState.

Definition Law := PersistentState -> TransactionRequest -> PersistentState.
Variable law : Law.


Record Machine : Type := {
  billboard : Collection.t;
  history : list PersistentState;
  now : PersistentState;
}.

Definition perform_request (m : Machine) (request : TransactionRequest) : Machine :=
  let (board, history, now) := m
  in Build_Machine (remove request board) (now::history) (law now request).

Definition add_request (m : Machine) (request : TransactionRequest) : Machine :=
  let (board, history, now) := m
  in Build_Machine (add request board) history now.

Definition empty_machine := Build_Machine empty [] startState.


Variable env : Machine -> TransactionRequest -> Prop.

Inductive machine_step : Machine -> Machine -> Prop :=
  | move_machine : forall m request, machine_step m (perform_request m request)
  | move_external : forall m request, env m request
                 -> Collection.mem request (billboard m) = false
                 -> machine_step m (add_request m request).

End MachineDef.


Parameter LocalPersistentState : Type.
Parameter Message : Type.

Definition SpecIdentity := nat.

Definition LocalTransferRelation := LocalPersistentState -> LocalPersistentState -> Prop.

Definition LocalStateMapping := SpecIdentity -> LocalPersistentState.
Definition LocalTransferMapping := SpecIdentity -> LocalTransferRelation.

(* TODO: mapping is appendable *)
(* local_transfer_mapping is a constraint on global_transfer_mapping *)

Definition compatible_transfer_mapping (sp1 sp2 : LocalTransferMapping) :=
  forall id1 id2 local1 local2,
  -> sp1 id' local1 local2
  -> sp2 id' local1 local2.









Definition Spec := (Identity -> LocalPersistentState) -> Message -> (LocalPersistentState * (Identity -> list Message)).
(* The intention is to apply it recursively, and ignore messages where ... *)

Record 

(* 
TODO:
1. Add structure to Law
2. Define games
*)
