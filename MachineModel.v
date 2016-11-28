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

