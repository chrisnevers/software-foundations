(* Days of the week *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday d :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

(* Booleans *)

Inductive bool : Type :=
  | true
  | false.

Definition negb b :=
  match b with
  | true  => false
  | false => true
  end.

Definition andb b1 b2 :=
  match b1 with
  | true  => b2
  | false => false
  end.

Definition orb b1 b2 :=
  match b1 with
  | true  => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb b1 b2 :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 b1 b2 b3 := andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Types *)

Check true.

Check (negb true).

Check negb.

(* New types from old *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome c :=
  match c with
  | black     => true
  | white     => true
  | primary _ => false
  end.

Definition is_red c :=
  match c with
  | primary red => true
  | _ => false
  end.

(* Tuples *)

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero nb :=
  match nb with
  | (bits B0 B0 B0 B) => true
  | (bits _  _  _  _) => false
  end.

(* Modules / Numbers *)
Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n: nat).

End NatPlayground.

Check (S (S (S (S O)))).

Definition minus_two n :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minus_two 4).

Fixpoint evenb n :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb n := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

Fixpoint plus n m :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Example test_exp: exp 2 3 = 8.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial n :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

Check ((0 + 1) + 1).

Fixpoint eqb n m :=
  match n, m with
  | O, O => true
  | O, S m' => false
  | S n', O => false
  | S n', S m' => eqb n' m'
  end.

Fixpoint leb n m :=
  match n, m with
  | O, _ => true
  | S n', O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof by Simplification *)

(*
  simpl - reduces both sides of the equation
  reflexivity - check that both sides contain identical values
*)

Theorem plus_O_n: forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

(*
  reflexivity does simplifying, even _more_ than
  simpl. It tries unfolding defined terms, replacing
  them with their rhs.

  Example, Theorem, Lemma, Fact and Remark are all
  more of less the same in Coq.
*)

Lemma plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Fact mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

(* Proof by Rewriting *)

(* For all natural numbers, when n and m are equal... *)
(* n = m is the hypothesis *)
(* n + n = m + m is the goal *)
Theorem plus_id_example: forall n m: nat, n = m ->
  n + n = m +  m.
Proof.
  (* Move both quantifiers into current context *)
  intros n m.
  (* Move the hypothesis into the context. *)
  intros H.
  (* Rewrite (-> means from left to right) the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.
Qed.

Fact plus_id_exercise: forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Lemma mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(* Proof by Case Analysis *)
Theorem plus_1_neq_0_first_try : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

(*
  Both eqb and + begin by performin a match on
  their first argument. Here, the first arg to
  + is the unknown number n and the arg to egb is
  the compound exp (n + 1). Neither can be simplified.
*)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  (*
    as [ | n] is an intro pattern
    list variables to bind for each constructor
    separated by | in []. O is nullary, and S n
    is unary.
  *)
  destruct n as [| n'] eqn:E.
  (* The - signs are called bullets, and mark each sub goal. *)
  - reflexivity.
  - reflexivity.
Qed.

(*
  Proof boolean negation is involutive - e.g. that negation
  is its own inverse.
*)
Remark negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

(* We can use -, +, *, and curly braces as bullets *)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Lemma andb3_exchange : forall b c d,
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true ->
  c = true.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(*
  This function is fine but coq thinks
  it will not terminate on all inputs.
Fixpoint does_not_term n :=
  match n with
  | O => O
  | m => does_not_term ( m - 1)
  end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall(x : bool), f x = x) ->
  forall(b : bool), f (f b) = b
.
Proof.
  intros f x H.
  rewrite x.
  rewrite x.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f: bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x H.
  rewrite -> x.
  rewrite -> x.
  rewrite <- negb_involutive.
  reflexivity.
Qed.

Theorem andb_eq_orb :
  forall b c : bool,
  andb b c = orb b c ->
  b = c.
Proof.
  intros [] c.
  - destruct c.
    + intros H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
  - destruct c.
    + simpl. intros H. rewrite H. reflexivity.
    + intros H. reflexivity.
  (* intros [] [].
  - intros H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity.
  - intros H. reflexivity. *)
Qed.

Inductive bin : Type :=
  | Z
  | A (n: bin)
  | B (n: bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z => B (Z)
  | A n => B n
  | B n => A (incr n)
  end.

Example test_incr1: incr Z = B Z.
Proof. simpl. reflexivity. Qed.
Example test_incr2: incr (B Z) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_incr3: incr (A (B Z)) = B (B Z).
Proof. simpl. reflexivity. Qed.
Example test_incr4: incr (A (A (B Z))) = B (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_incr5: incr (B (B (B Z))) = A (A (A (B Z))).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z   => 0
  | B Z => 1
  | B n => 1 + (2 * bin_to_nat n)
  | A n => 2 * bin_to_nat n
  end.

Example test_bin_to_nat1: bin_to_nat Z = 0.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat2: bin_to_nat (B Z) = 1.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat3: bin_to_nat (A (B Z)) =2.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat4: bin_to_nat (B (B Z)) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat5: bin_to_nat (B (A (B Z))) = 5.
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat6: bin_to_nat (A (A (A (B Z)))) = 8.
Proof. simpl. reflexivity. Qed.
