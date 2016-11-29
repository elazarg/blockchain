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

End ArenaDef.
