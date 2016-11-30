Require Import Bool List.

Require Import Arith.PeanoNat FSets.FMapWeakList.
Module Import MapNat := FMapWeakList.Make Nat.

Section MachineDef.

Definition AgentId := nat.
Definition AgentMap := MapNat.t.
Definition BusinessId := nat.
Definition BusinessMap := MapNat.t.

Variable LocalPState : Type.
Definition GlobalPState := BusinessMap LocalPState.

Section Deal.
(* TODO: perhaps not a BusinessMap but a RoleMap *)
(* A deal is a 'lockstep' of group of businesses *)
Definition Deal := BusinessMap (LocalPState * LocalPState).
(* Policies must be encoded in the local state, so other policies can depend on them *)
Definition PolicyExtractor := LocalPState -> (Deal -> Prop).

Definition unzip_deal (deal : Deal) := (map fst deal, map snd deal).

Parameter (allows : PolicyExtractor).

(* Perhaps we may need to approve only the resulting state *)
(* The inductive definition is only here to say "legal deals are superset-closed" *)
Inductive step_legal_deal (me : BusinessId) (deal : Deal) : Prop :=
  | base : forall start finish,
           find me deal = Some (start, finish)
        -> allows start deal
        -> step_legal_deal me deal
  | step : forall partial_deal,
           step_legal_deal me partial_deal
        -> partial_deal = remove me deal
        -> step_legal_deal me deal.

Definition step_consistent_deal (deal : Deal) : Prop :=
  forall (b : BusinessId), step_legal_deal b deal.

Definition composed_deals (d1 d2 res : Deal) : Prop :=
  let '(a, b1) := unzip_deal d1 in
  let '(b2, c) := unzip_deal d2 in
  forall id a b, MapsTo id b1 a -> MapsTo id b2 b -> a = b.


(* A deal is consistent if it can be seen as a sequence of deals such that
   each deal is step-consistent. (sadly, the second constructor is not uniquely defined) *)
Inductive consistent_deal (deal : Deal) : Prop :=
  | consistent_base : step_consistent_deal deal
                        -> consistent_deal deal
  | consistent_compose (d1 d2 : Deal) : composed_deals d1 d2 deal
                        -> consistent_deal deal.


End Deal.

Definition Request : Type := LocalPState * LocalPState.
(* business_of owner -> someother -> transitio *)
Parameter business_of : AgentId -> BusinessId.

Record Machine : Type := {
  billboard : AgentMap Request;
  history : list GlobalPState;
  now : GlobalPState;
}.

(* TODO: add state *)
Parameter agents : AgentMap (Machine -> Request).

Variable startState : GlobalPState.

Definition add_request (owner : AgentId) (request : Request) (m : Machine) : Machine :=
  Build_Machine (add owner request (billboard m)) (history m) (now m).

Inductive machine_step : Machine -> Machine -> Prop :=
  | move_machine (owner : AgentId) (m1 m2: Machine) :
                   billboard m2 = remove owner (billboard m1)
                -> history m2 = (now m1)::(history m1)
                -> (exists deal, unzip_deal deal = (now m1, now m2) /\ consistent_deal deal)
                -> machine_step m1 m2
  | move_external (owner : AgentId) (request : Request) (m1 : Machine) :
                    Some request = find owner (map (fun s => s m1) agents)
                 -> mem owner (billboard m1) = false
                 -> machine_step m1 (add_request owner request m1).


Definition SocialRequirements := BusinessId -> LocalPState -> LocalPState -> Prop.

End MachineDef.
