From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import HOASNotation.

Open Scope string_scope.
Open Scope example_scope.


Definition choreo : Choreography.t :=
  mk (
    do q ← "alice" [- Unitary H (New (Bit false))-] ;;
    teleport "alice" "bob" q
  ).

Eval compute in choreo.

Eval compute in (Network.epp "alice" choreo).
(*
  do q ← Unitary H (New (Bit false)) ;;
  do a ← establish_entanglement Bob ;;
  do (q,a) ← Unitary CNOT (q,a) ;;
  do q ← unitary H q ;;
  do x ← Meas q ;;
  do z ← Meas a ;;
  do _ ← Send Bob x ;;
  Send Bob z
*)


Eval compute in (Network.epp "bob" choreo).
(*
  do b ← establish_entanglement Alice ;;
  do x ← Receive Alice ;;
  do z ← Receive Alice ;;
  do b ← If z (Unitary Z b) b ;;
  If x (Unitary X b) b
*)


Eval compute in (Network.epp "bob" choreo).


Definition parties : list Actor.t :=
  ["alice"; "bob"].


Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "teleportation_netqasm.ml" apps.
