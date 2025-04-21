Theorem zero_plus_n : forall n : nat, 0 + n = n.
Proof.
  intros n. (* Introduce the natural number n *)
  simpl.    (* Simplify 0 + n using definition of addition *)
  reflexivity. (* LHS and RHS are equal, so we conclude the proof *)
Qed.
