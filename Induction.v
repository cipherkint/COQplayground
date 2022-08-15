From LF Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* 虽然目前还没啥问题... *)
  - (* n = S n' *)
    simpl. (* ...不过我们又卡在这儿了 *)
Abort.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* 课上已完成 *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - induction m as [| m' IHm'].
    + simpl. rewrite -> IHn'. reflexivity.
    + simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  induction m as [| m' IHm'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHm'. simpl. reflexivity.
  - simpl. rewrite -> IHn'. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.

Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - induction m as [| m' IHm'].
    + simpl. rewrite <- IHn'. simpl. reflexivity.
    + induction p as [| p' IHp'].
      * simpl. rewrite <- IHn'. simpl. reflexivity.
      * simpl. rewrite <- IHn'. simpl. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.
  
(*请简要说明一下 destruct 策略和 induction 策略之间的区别。*)
(* Deductive -> “由大到小” *)
(* Inductive -> “由小到大” *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只需要将 (m + n) 交换为 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 搞不定... Coq 选错了要改写的加法！ *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  rewrite -> plus_assoc. reflexivity.
Qed.

Check mult_n_Sm.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite <- mult_n_O. simpl. reflexivity.
  - rewrite <- mult_n_Sm. rewrite <- IHn'. simpl. rewrite -> plus_comm.
  reflexivity.
Qed.
  

Check leb.
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  - reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H. 
  induction p as [| p'].
    - simpl. rewrite -> H. reflexivity.
    - simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  simpl. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  simpl.
  intros n.
  rewrite <- plus_n_O.
  reflexivity.
  Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.
  

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - rewrite -> plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity.
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

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => plus (bin_to_nat m') (bin_to_nat m')
  | B m' => S (plus (bin_to_nat m') (bin_to_nat m'))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [| b'| b''].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHb''. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.


Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
Qed. 

(*----------------------------n o r m a l i z a t i o n------------------------------------*)

Definition mult_bin_ABZ (m:bin) : bin :=
  match m with
  | Z => Z
  | A m' => A (A m')
  | B m' => A (B m')
  end.

Fixpoint bin_normalization (m:bin) : bin :=
  match m with
  | Z => Z
  | A m' => mult_bin_ABZ (bin_normalization m')
  | B m' => incr (mult_bin_ABZ (bin_normalization m'))
  end.

Compute (bin_normalization (A (B (B Z)))).

Theorem  twice_mult_change : forall b, mult_bin_ABZ (incr b) = incr (incr (mult_bin_ABZ b)).
Proof.
  intros b. induction b as [| b'| b''].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem twice_nat_to_bin_change : forall n, mult_bin_ABZ (nat_to_bin n) =  nat_to_bin (n * 2).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. rewrite -> twice_mult_change. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = bin_normalization b.
Proof.
  intros b. induction b as [| b'| b''].
  - simpl. reflexivity.
  - simpl. rewrite <- IHb'. rewrite <- mult_n_2. rewrite-> twice_nat_to_bin_change. reflexivity.
  - simpl. rewrite <- IHb''. rewrite <- mult_n_2. rewrite-> twice_nat_to_bin_change. reflexivity.
Qed.