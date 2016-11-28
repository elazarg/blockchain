Require Import MachineModel.
Require Import Arith.PeanoNat.

Require Import
  FSets.FMapWeakList
  FSets.FSetWeakList
  Structures.DecidableType.

Module Import Map := FMapWeakList.Make Nat.
Definition Identity := nat.

Definition Strategy := Machine -> TransactionRequest.

Inductive arena_step (agents : Map.t Strategy) (m m' : Machine) : Prop :=
  | move_machine : forall request, m <> m' /\ m' = perform_request m request
                   -> arena_step agents m m'
  | move_agents : forall request agent,
                  Some request = find agent (map (fun s => s m) agents)
                  -> Collection.mem request (billboard m) = false
                  -> m' = add_request m request
                  -> arena_step agents m m'.

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