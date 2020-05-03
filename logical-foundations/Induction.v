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

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <-plus_n_O. reflexivity.
  - rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - rewrite plus_O_n. simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double n :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negation_fn_applied_twice.
    + simpl. reflexivity.
    + reflexivity.
Qed.

(* Proofs within Proofs *)
