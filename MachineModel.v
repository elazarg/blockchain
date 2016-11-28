Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Arith.PeanoNat.
Require Import Relations.Relation_Definitions.

Require Import FSets.FSetWeakList.

Module Import Collection := FSetWeakList.Make Nat.
Definition TransactionRequest := nat.

Parameter PersistentState : Type.

Parameter startState : PersistentState.
Parameter law : PersistentState -> TransactionRequest -> PersistentState.


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
