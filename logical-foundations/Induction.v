From LF Require Export Basics.


(* Proof by Induction *)

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n, n * 0 = 0.
Proof.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

