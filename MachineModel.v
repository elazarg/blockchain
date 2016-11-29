Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Arith.PeanoNat.
Require Import Relations.Relation_Definitions.

Require Import Arith.PeanoNat.
Require Import FSets.FMapWeakList.

Module Import Map := FMapWeakList.Make Nat.

Section MachineDef.


Definition AgentIdentity := nat.
Definition SpecIdentity := nat.

Variable MessageContent : Type.
Variable LocalPersistentState : Type.

Definition GlobalPersistentState := SpecIdentity -> LocalPersistentState.

Parameter spec_of : AgentIdentity -> SpecIdentity.

(* spec_of owner -> someother -> transition *)
Variable law : SpecIdentity -> SpecIdentity -> LocalPersistentState -> LocalPersistentState -> Prop.
Variable startState : GlobalPersistentState.

Definition Request : Type := LocalPersistentState * LocalPersistentState.

Record Machine : Type := {
  billboard : Map.t Request;
  history : list GlobalPersistentState;
  now : GlobalPersistentState;
}.

Definition add_request (owner : AgentIdentity) (request : Request) (m : Machine) : Machine :=
  Build_Machine (add owner request (billboard m)) (history m) (now m).


Definition Env : Type := Machine -> AgentIdentity -> Request -> Prop.

Inductive machine_step (env : Env) : Machine -> Machine -> Prop :=
  | move_machine (owner : AgentIdentity) : forall (m1 m2: Machine),
                   (billboard m2) = remove owner (billboard m1)
                -> (history m2) = (now m1)::(history m1)
                -> forall spec, law (spec_of owner) spec (now m1 spec) (now m2 spec)
                -> machine_step env m1 m2
  | move_external : forall m owner request, env m owner request
                 -> mem owner (billboard m) = false
                 -> machine_step env m (add_request owner request m).


Definition Strategy := Machine -> Request.

(* TODO: add state *)
Definition Agent := Strategy.

Variable (agents : Map.t Agent).

Definition agents_relation (m : Machine) (owner : AgentIdentity) (request : Request) : Prop :=
  Some request = find owner (map (fun s => s m) agents).

Definition arena_step : Machine -> Machine -> Prop := machine_step agents_relation.

End MachineDef.


(* Note: the following allows behaviors that cannot happen in practice *)

Parameter LocalPersistentState : Type.
Parameter Message : Type.

Definition SpecIdentity := nat.

Definition LocalTransferRelation := LocalPersistentState -> LocalPersistentState -> Prop.

Definition LocalStateMapping := SpecIdentity -> LocalPersistentState.
Definition LocalTransferMapping := SpecIdentity -> LocalTransferRelation.

(* TODO: mapping is appendable *)
(* local_transfer_mapping is a constraint on global_transfer_mapping *)

(* spec1 belongs to id1, and is compatible with spec2 if for any other identity id2 it cannot perform a transfers
   that is not allowed by spec2 *)
Definition compatible_transfer_mapping (id1 : SpecIdentity) (sp1 sp2 : LocalTransferMapping) : Prop :=
  forall id' local'1 local'2, id' <> id1 
  -> sp1 id' local'1 local'2
  -> sp2 id' local'1 local'2.


(*







Definition Spec := (Identity -> LocalPersistentState) -> Message -> (LocalPersistentState * (Identity -> list Message)).
(* The intention is to apply it recursively, and ignore messages where ... *)

*)

(* 
TODO:
1. Add structure to Law
2. Define games
*)
