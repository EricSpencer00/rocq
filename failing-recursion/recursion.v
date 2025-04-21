Require Import Arith.

Fixpoint ack (m n : nat) : nat :=
  match m, n with
  | 0, _ => n + 1
  | S m', 0 => ack m' 1
  | S m', S n' => ack m' (ack m' n')
  end.
