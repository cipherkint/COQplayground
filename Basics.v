Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Compute (negb true).

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Compute (andb true false).

Definition orb (b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute (orb true false).

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_and1:
  (true && false && true) = false.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Compute (negb' true).

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Compute (andb' true true).


Definition nandb (b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true
    : bool.
Check (negb true)
    : bool.

Check negb.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color): bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
    : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Compute (pred 3).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Compute (evenb 4).
Compute (evenb 5).
Compute (evenb (S (S O))).

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 5 3).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Compute (exp 3 5).

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S p => mult (plus p 1) (factorial p)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y).
Notation "x - y" := (minus x y).
Notation "x * y" := (mult x y).

Check ((0 + 1) + 1).
  
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
         | O => false
         | S m' => eqb n' m'
         end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool:=
  match (minus n m) with 
  | O => (negb(eqb n m))
  | _ => false
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Compute (minus 3 5).

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* 将两个量词移到上下文中： *)
  intros n m.
  (* 将前提移到上下文中： *)
  intros H.
  (* 用前提改写目标： *)
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> 
  m = o -> 
  n + m = m + o.
Proof.
  intros n m o.
  intros H J.
  rewrite -> H.
  rewrite -> J.
  reflexivity. Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall n m : nat,
  (n * 0) + (m * 0) = 0.

Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_2 : forall n : nat,
  n * 2 = n + n.
Proof.
  intros.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* 无能为力! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

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

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
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
  - reflexivity. Qed.

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
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c.
  - simpl. intros H. reflexivity.
  - rewrite -> andb_commutative.
               simpl.
               intros H.
               rewrite H.
               reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(*
Fixpoint funny_func (n : nat) (m : nat) : nat :=
  match n with
  | 0 => (funny_func (minus m 1) 1)
  | S n' => (funny_func (minus m 1) (funny_func m (minus n' 1)))
  end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros x. destruct x eqn : Ex.
  - rewrite H. rewrite H. reflexivity.
  - rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool),  f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros x. destruct x eqn : Ex.
  - rewrite H. rewrite H. reflexivity.
  - rewrite H. rewrite H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b. destruct b eqn : Eb.
  intros c. destruct c eqn : Ec.
  - reflexivity. 
  - simpl.
    * intros H.
      + rewrite H. reflexivity.
  - intros c. destruct c eqn : Ec.
    * simpl.
      + intros H.
        rewrite H. reflexivity.
    * reflexivity. 
Qed.
  
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.

Compute (incr (A (B (B Z)))).

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => plus (bin_to_nat m') (bin_to_nat m')
  | B m' => S (plus (bin_to_nat m') (bin_to_nat m'))
  end.

Compute (bin_to_nat (A (A (B Z)))).

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
