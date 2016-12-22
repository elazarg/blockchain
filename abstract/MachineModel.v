Require Import Bool List.

Require Import Arith.PeanoNat FSets.FMapWeakList.

Variable LocalPState : Type.

Module Import MapNat := FMapWeakList.Make Nat.

Section MachineDef.

Definition BusinessId := nat.
Definition BusinessMap := MapNat.t.

Definition GlobalPState := BusinessMap LocalPState.

Section Deal.
(* A deal is a 'lockstep' of group of businesses *)
(* TODO: perhaps not a BusinessMap but a RoleMap *)
Definition Deal := BusinessMap (LocalPState * LocalPState).
(* Policies must be encoded in the local state, so other policies can depend on them *)
Definition PolicyExtractor := LocalPState -> (Deal -> Prop).

Definition unzip_deal (deal : Deal) := (map fst deal, map snd deal).

Parameter (allows : PolicyExtractor).

(* Perhaps we may need to approve only the resulting state *)
(* The inductive definition is only here to say "legal deals are superset-closed" *)
Definition step_legal_deal (me : BusinessId) (deal : Deal) : Prop :=
  exists partial_deal,
       (forall k v, MapsTo k v partial_deal -> MapsTo k v deal)
    /\ (exists start finish, MapsTo me (start, finish) partial_deal /\ allows start partial_deal).

Definition composed_deals (d1 d2 res : Deal) : Prop :=
  let '(a, b1) := unzip_deal d1 in
  let '(b2, c) := unzip_deal d2 in
  forall id a b, MapsTo id b1 a -> MapsTo id b2 b -> a = b.


(* A deal is consistent if it can be seen as a sequence of deals such that
   each deal is step-consistent. (sadly, the second constructor is not uniquely defined) *)
Inductive consistent_deal (deal : Deal) : Prop :=
  | consistent_base : forall (b : BusinessId), step_legal_deal b deal
                        -> consistent_deal deal
  | consistent_compose (d1 d2 : Deal) : composed_deals d1 d2 deal
                        -> consistent_deal deal.


End Deal.

Record Machine : Type := {
  history : list GlobalPState;
  now : GlobalPState;
}.

Inductive machine_step : Machine -> Machine -> Prop :=
  | move_machine (m1 m2: Machine) :
                   history m2 = (now m1)::(history m1)
                -> (exists deal, unzip_deal deal = (now m1, now m2) /\ consistent_deal deal)
                -> machine_step m1 m2.

Variable startState : GlobalPState.
End MachineDef.

Section ArenaDef.

Definition AgentId := nat.
Definition AgentMap := MapNat.t.
(* business_of owner -> someother -> transitio *)

Definition Request : Type := LocalPState * LocalPState.


Parameter business_of : AgentId -> BusinessId.

Record Arena : Type := {
  billboard : AgentMap Request;
  machine : Machine;
}.
(* TODO: add state *)
Variable agents_actions : AgentMap (Arena -> Request).

Definition add_request (owner : AgentId) (request : Request) (a : Arena) : Arena :=
  Build_Arena (add owner request (billboard a)) (machine a).

Inductive arena_step : Arena -> Arena -> Prop :=
  | exec_request (owner : AgentId) (request : Request) : forall a1 a2,
                   billboard a2 = remove owner (billboard a1)
                 -> machine_step (machine a1) (machine a2)
                 -> arena_step a1 a2
  | agent_act (owner : AgentId) (request : Request) : forall (a1 : Arena),
                    Some request = find owner (map (fun s => s a1) agents_actions)
                 -> mem owner (billboard a1) = false
                 -> arena_step a1 (add_request owner request a1).

End ArenaDef.
