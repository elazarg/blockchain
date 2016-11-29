Require Import Bool.
Require Import List.
Import ListNotations.

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

Definition LocalTransition := SpecIdentity -> LocalPersistentState -> LocalPersistentState -> Prop.
(* spec_of owner -> someother -> transition *)
Variable startState : GlobalPersistentState.

Definition Request : Type := LocalPersistentState * LocalPersistentState.

Record Machine : Type := {
  billboard : Map.t Request;
  history : list GlobalPersistentState;
  now : GlobalPersistentState;
  law : SpecIdentity -> LocalTransition;
}.

Definition add_request (owner : AgentIdentity) (request : Request) (m : Machine) : Machine :=
  Build_Machine (add owner request (billboard m)) (history m) (now m) (law m).


Definition Env : Type := Machine -> AgentIdentity -> Request -> Prop.

Inductive machine_step (env : Env) : Machine -> Machine -> Prop :=
  | move_machine (owner : AgentIdentity) : forall (m1 m2: Machine),
                   (billboard m2) = remove owner (billboard m1)
                -> (history m2) = (now m1)::(history m1)
                -> forall spec, (law m1) (spec_of owner) spec (now m1 spec) (now m2 spec)
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

Definition arena_step := machine_step agents_relation.

End MachineDef.
