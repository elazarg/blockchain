Require Import Bool List.

Require Import Arith.PeanoNat FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.

Section MachineDef.

Definition AgentId := nat.
Definition AgentMap := MapNat.t.
Definition SpecId := nat.
Definition SpecMap := MapNat.t.

Variable LocalPState : Type.
Definition GlobalPState := SpecId -> LocalPState.
Definition Request : Type := LocalPState * LocalPState.
(* spec_of owner -> someother -> transition *)

Record Machine : Type := {
  billboard : AgentMap Request;
  history : list GlobalPState;
  now : GlobalPState;
}.

(* TODO: add state *)
Variable agents : AgentMap (Machine -> Request).

Parameter spec_of : AgentId -> SpecId.
Variable startState : GlobalPState.

(* TODO: perhaps not a SpecMap but a RoleMap *)
Definition Deal := SpecMap (LocalPState * LocalPState).
(* Policies must be encoded in the local state, so other policies can depend on them *)
Definition SingleBusinessPolicy := LocalPState -> (Deal -> Prop).

Variable lawbook : SpecMap (SpecId -> SingleBusinessPolicy).

Definition add_request (owner : AgentId) (request : Request) (m : Machine) : Machine :=
  Build_Machine (add owner request (billboard m)) (history m) (now m).

Inductive machine_step : Machine -> Machine -> Prop :=
  | move_machine (owner : AgentId) (m1 m2: Machine) :
                   billboard m2 = remove owner (billboard m1)
                -> history m2 = (now m1)::(history m1)
                -> forall spec_id, law (spec_of owner) spec_id (now m1 spec) (now m2 spec_id)
                -> machine_step m1 m2
  | move_external (owner : AgentId) (request : Request) (m1 : Machine) :
                    Some request = find owner (map (fun s => s m1) agents)
                 -> mem owner (billboard m1) = false
                 -> machine_step m1 (add_request owner request m1).


Definition SocialRequirements := SpecId -> LocalPState -> LocalPState -> Prop.

End MachineDef.
