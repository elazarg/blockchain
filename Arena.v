Require Import MachineModel.
Require Import Arith.PeanoNat.

Require Import FSets.FMapWeakList.

Module Import Map := FMapWeakList.Make Nat.

Section ArenaDef.

Definition Identity := nat.

Definition Strategy := Machine -> TransactionRequest.

(* TODO: add state *)
Definition Agent := Strategy.

Variable law : Law.
Variable (agents : Map.t Agent).

Definition agents_relation (m : Machine) (request : TransactionRequest) : Prop :=
  exists id, Some request = find id (map (fun s => s m) agents).

Definition arena_step : Machine -> Machine -> Prop := machine_step law agents_relation.

Inductive arena_step1 : Machine -> Machine -> Prop :=
  | move_machine : forall m request, arena_step m (perform_request law m request)
  | move_agent (agent : Identity) : forall m request,
                 Some request = find agent (map (fun s => s m) agents)
                 -> Collection.mem request (billboard m) = false
                 -> arena_step m (add_request m request).

End ArenaDef.

Axiom a : Agent.

Definition simul_game (l : Law) (start : Machine) (p1 p2 : Agent) (win : Machine -> Prop) : Prop :=
  let agents := add 2 p2 (add 1 p1 (Map.empty Agent)) in
  .

Proposition no_simul_agree :
  forall (a1 : Agent), exists (a2 : Agent),
  