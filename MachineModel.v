Require Import Bool.
Require Import List.
Import ListNotations.

Require Import Arith.PeanoNat.
Require Import FSets.FMapWeakList.

Module Import Map := FMapWeakList.Make Nat.

Section MachineDef.

Definition AgentId := nat.
Definition SpecId := nat.
Variable LocalPState : Type.
Definition GlobalPState := SpecId -> LocalPState.
Definition Request : Type := LocalPState * LocalPState.
(* spec_of owner -> someother -> transition *)

Record Machine : Type := {
  billboard : Map.t Request;
  history : list GlobalPState;
  now : GlobalPState;
}.

Parameter spec_of : AgentId -> SpecId.
Variable startState : GlobalPState.
Variable law : SpecId -> SpecId -> LocalPState -> LocalPState -> Prop.
(* TODO: add state *)
Variable agents : Map.t (Machine -> Request).

Definition add_request (owner : AgentId) (request : Request) (m : Machine) : Machine :=
  Build_Machine (add owner request (billboard m)) (history m) (now m).

Inductive machine_step : Machine -> Machine -> Prop :=
  | move_machine (owner : AgentId) (m1 m2: Machine) :
                   billboard m2 = remove owner (billboard m1)
                -> history m2 = (now m1)::(history m1)
                -> forall spec, law (spec_of owner) spec (now m1 spec) (now m2 spec)
                -> machine_step m1 m2
  | move_external (owner : AgentId) (request : Request) (m1 : Machine) :
                    Some request = find owner (map (fun s => s m1) agents)
                 -> mem owner (billboard m1) = false
                 -> machine_step m1 (add_request owner request m1).

End MachineDef.
