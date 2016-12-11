Require Import Bool List.

Require Import Arith.PeanoNat FSets.FMapWeakList.

Variable LocalPState : Type.

Module Import MapNat := FMapWeakList.Make Nat.

Section MachineDef.

Definition BusinessId := nat.
Definition BusinessMap := MapNat.t.

Definition GlobalPState := BusinessMap LocalPState.

Section Deal.

Definition Deal := (BusinessId * BusinessId * BusinessId) % type.
Parameter allows : BusinessId -> (BusinessId * BusinessId) -> option LocalPState.

Definition step_legal_deal (me : BusinessId) (deal : Deal) : Prop :=
  let '(a, b, c) := deal in
     (me = a /\ (allows me (b, c) <> None \/ allows me (c, b) <> None))
  \/ (me = b /\ (allows me (a, c) <> None \/ allows me (c, a) <> None))
  \/ (me = c /\ (allows me (a, b) <> None \/ allows me (b, a) <> None)).

Definition consistent_deal (deal : Deal) : Prop :=
  let '(a, b, c) := deal in
  step_legal_deal a deal /\ step_legal_deal b deal /\ step_legal_deal c deal.


End Deal.

Record Machine : Type := {
  history : list Deal;
}.

Inductive machine_step : Machine -> Machine -> Prop :=
  .

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
