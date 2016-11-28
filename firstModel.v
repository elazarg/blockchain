Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Arith.PeanoNat.
Require Import Relations.Relation_Definitions.

Require Import
  FSets.FMapWeakList
  FSets.FSetWeakList
  Structures.DecidableType.

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

Module Import Map := FMapWeakList.Make Nat.
Definition Identity := nat.

Definition Strategy := Machine -> TransactionRequest.

Record Game : Type := {
  agents : Map.t Strategy;
  machine : Machine;
}.

Inductive game_step (agents : Map.t Strategy) (g g' : Game) : Prop :=
  | move_machine : forall m m' request,
                   m <> m' /\ m' = perform_request m request
                   -> g = (Build_Game agents m) /\ g' = (Build_Game agents m')
                   -> game_step agents g g'
  | move_agents : forall request agent,
                  Some request = find agent (map (fun s => s (machine g)) agents)
                  -> Collection.mem request (billboard (machine g)) = false
                  -> g = (Build_Game agents (machine g)) /\ g' = (Build_Game agents (add_request (machine g) request))
                  -> game_step agents g g'.

(*
Decisions:
  * keep state and not a list of transactions. The only difference is knowledge about past transactions.

  * Ideal model: Transactions as (pre-state, post-state) pairs? Perhaps we need separation logic for locality.
                 Kripke structure, and transaction is (p, q) for some predicates.
*)

(*
Not in the model:
* Contracts
* Structure of a persistent state
* Money (a property of a contract?)
* knowledge and belief of agents
* Miners
* Gas
* Cryptography
* Probabilities

*)