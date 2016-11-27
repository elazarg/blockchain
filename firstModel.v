Require Import Bool.
Require Import List.
Import ListNotations.
Require Lists.ListSet.
Require Import Coq.Relations.Relation_Definitions.

Parameter TransactionRequest : Type.
Hypothesis TXeq_dec : forall x y : TransactionRequest, {x = y} + {x <> y}.

Parameter PersistentState : Type.
Parameter startState : PersistentState.

Parameter law : PersistentState -> TransactionRequest -> PersistentState.

Definition set := ListSet.set.
Definition set_remove := ListSet.set_remove TXeq_dec.
Definition set_add := ListSet.set_add TXeq_dec.
Definition set_mem := ListSet.set_mem TXeq_dec.



Record Model : Type := {
  billboard : set TransactionRequest;
  history : list PersistentState;
  now : PersistentState;
}.

Definition empty_model := {|
  billboard := ListSet.empty_set TransactionRequest;
  history := [];
  now := startState;
|}.

Definition perform_request (m : Model) (request : TransactionRequest) : Model :=
  let (board, history, now) := m
  in Build_Model (set_remove request board) (now::history) (law now request).

Definition add_request (m : Model) (request : TransactionRequest) : Model :=
  let (board, history, now) := m
  in Build_Model (set_add request board) history now.

Inductive Run : Model -> Type :=
  | empty : Run empty_model
  | tx_publish : forall m, Run m
              -> forall req, Run (add_request m req)
  | tx_perform : forall m, Run m
              -> forall request, set_mem request (billboard m) = true
                 -> Run (perform_request m request).


(*
Decisions:
  * keep state and not a list of transactions. The only difference is knowledge about past transactions.

  * Agents strategy -
    Definition Strategy := Billboard -> Trace -> TransactionRequest.
    Parameter agents : list Strategy. (* actually, agent_strategies. *)

  * Ideal model: Transactions as (pre-state, post-state) pairs? Perhaps we need separation logic for locality.
                 Kripke structure, and transaction is (p, q) for some predicates.
*)

(*
Not in the model:
* Structure of a persistent state
* Miners
* Money
* Gas
* Cryptography
* Probabilities

*)