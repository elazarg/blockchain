Require Import Bool List.

Require Import Arith.PeanoNat FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.

Section MachineDef.

Definition AgentId := nat.
Definition AgentMap := MapNat.t.
Definition SpecId := nat.
Definition SpecMap := MapNat.t.

Variable LocalPState : Type.
Definition GlobalPState := SpecMap LocalPState.

Section Deal.
(* TODO: perhaps not a SpecMap but a RoleMap *)
(* A deal is a 'lockstep' of group of businesses *)
Definition Deal := SpecMap (LocalPState * LocalPState).
(* Policies must be encoded in the local state, so other policies can depend on them *)
Definition PolicyExtractor := LocalPState -> (Deal -> Prop).

Variable  (allows : PolicyExtractor).

(* Perhaps we may need to approve only the resulting state *)
(* The inductive definition is only here to say "legal deals are superset-closed" *)
Inductive step_legal_deal (me : SpecId) (deal : Deal) : Prop :=
  | base : forall start finish,
           find me deal = Some (start, finish)
        -> allows start deal
        -> step_legal_deal me deal
  | step : forall partial_deal,
           step_legal_deal me partial_deal
        -> partial_deal = remove me deal
        -> step_legal_deal me deal.

Definition step_consistent_deal (deal : Deal) : Prop :=
  forall (spec_id : SpecId), step_legal_deal spec_id deal.

Definition composable_deals (d1 d2 : Deal) : Prop :=
  forall (id : SpecId) start mid finish,
  let t1 := find id d1 in
  let t2 := find id d2 in
  t1 = Some (start, mid) /\ t2 = Some (mid, finish)
  \/ t1 = None
  \/ t2 = None.


(* A deal is consistent if it can be seen as a sequence of deals such that
   each deal is step-consistent. *)
Definition consistent_deal (deal : Deal) : Prop :=
  .

End Deal.

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
