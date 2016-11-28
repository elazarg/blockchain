Require Import Bool.
Require Import List.
Import ListNotations.
Require Lists.ListSet.
Require Import Coq.Relations.Relation_Definitions.

Require Import MachineModel.

Module Type Agent.

Definition Strategy := Machine -> TransactionRequest.

Parameter t: Type.
Parameter m: Machine.

Axiom peek : t.
Axiom act : Machine.

End Agent.