(* TestFMapAVL.v *)

(**
   Tiny client using Coq’s standard library finite maps (FMapAVL with nat keys).
   This example compiles out-of-the-box.
**)

From Coq Require Import OrderedTypeEx.
From Coq Require Import FMapAVL.
From Coq Require Import FMapFacts.

Module NatMap := FMapAVL.Make(Nat_as_OT).
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Import NatMap.

(* Test: adding and finding in a finite map *)
Goal forall (m : t nat) (k : key) (v : nat),
  find k (add k v m) = Some v.
Proof.
  intros m k v.
  apply NatMapFacts.add_eq_o.
  reflexivity.
Qed.
