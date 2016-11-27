Require Import Bool.
Require Import List.
Import ListNotations.
Require Lists.ListSet.
Require Import Coq.Relations.Relation_Definitions.

Parameter TransactionRequest : Type.
Hypothesis Aeq_dec : forall x y : TransactionRequest, {x = y} + {x <> y}.

Parameter PersistentState : Type.
Parameter startState : PersistentState.
Definition Trace := list PersistentState.
Definition Law := PersistentState -> TransactionRequest -> PersistentState.

Parameter contracts : Law.

Definition Billboard := ListSet.set TransactionRequest.
Definition set_remove := ListSet.set_remove Aeq_dec.
Definition set_add := ListSet.set_add Aeq_dec.
Definition set_mem := ListSet.set_mem Aeq_dec.

Definition Strategy := Billboard -> Trace -> TransactionRequest.
Parameter agents : list Strategy. (* actually, agent_strategies. optional? *)


Record Model : Type := mkModel {
  billboard : Billboard;
  trace : Trace;
  current : PersistentState; (* only here to avoid dealing with empty lists *)
}.

Definition empty_model := {|
  billboard := ListSet.empty_set TransactionRequest;
  trace := [];
  current := startState; 
|}.

Definition perform_request (m : Model) (req : TransactionRequest) : Model :=
  {|
    billboard := set_remove req (billboard m);
    trace := (current m)::(trace m);
    current := contracts (current m) req;
  |}.

Definition add_request (m : Model) (req : TransactionRequest) : Model :=
  {|
    billboard := set_add req (billboard m);
    trace := trace m;
    current := current m
  |}.

Inductive Run : Model -> Type :=
  | empty : Run empty_model
  | tx_publish : forall m, Run m
              -> forall req, Run (add_request m req)
  | tx_perform : forall m, Run m
              -> forall req, set_mem req (billboard m) = true
                 -> Run (perform_request m req).


(*
Not in the model:
* Structure of a persistent state
* Miners
* Money
* Gas
* Cryptography
* Probabilities

*)