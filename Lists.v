From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute (repeat 3 5).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Compute (length [1;2;3]).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Compute (app [1;2;3] [4;5;6]).

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
    match h with
    | O => nonzeros t
    | _ => h :: nonzeros t
    end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.
Set Nested Proofs Allowed.
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
    match h with
    | O => oddmembers(t)
    | nat => 
      match evenb(nat) with
      | true => oddmembers t
      | false => h :: oddmembers(t)
      end
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.
Definition countoddmembers (l:natlist) : nat :=
  match l with
  | k => length (oddmembers k)
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => 
    match l2 with
    | nil => h1 :: t1
    | h2 :: t2 => [ h1 ; h2 ] ++ (alternate t1 t2)
    end
  end.
  
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: s' => 
    match v =? h with
    | true => S (count v s')
    | false => (count v s')
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum (s1 s2 : bag) : bag :=
  match s1 with
  | nil => s2
  | h :: t => s1 ++ s2
  end.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  match s with
  | nil => [v]
  | h :: t => [v] ++ s
  end.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Compute (add 1 [1;2;5]).
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match s with
  | nil => false
  | h :: t => 
    match h =? v with
    | true => true
    | false => false
    end
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match h =? v with
    | true => t
    | false => h :: (remove_one v t)
    end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match h =? v with
    | true => (remove_all v t)
    | false => h :: (remove_all v t)
    end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => 
    match (count h s1) <=? (count h s2) with
    | true => subset t s2
    | false => false
    end
  end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* count add *)
Theorem bag_theorem : forall (s : bag) (n : nat),
S(count n s) = count n (add n s).
Proof.
  intros s n. induction n as [| n'].
  - induction s.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction s.
    + simpl. rewrite <- eqb_refl. reflexivity.
    + simpl. rewrite <- eqb_refl. reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* 课上已完成 *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.

Search rev.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl1'. simpl. reflexivity.
Qed.

Search app.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite <- app_assoc. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - induction l2 as [| n2 l2' IHl2'].
    + rewrite -> app_nil_r. simpl. rewrite -> app_nil_r. reflexivity.
    + simpl. rewrite -> IHl1'. simpl. 
      destruct n as [| n'] eqn:E.
      * reflexivity.
      * simpl. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => 
    match l2 with
    | nil => true
    | h2 :: t2 => false
    end
  | h1 :: t1 =>
    match l2 with
    | nil => false
    | h2 :: t2 => 
      match h1 =? h2 with
      | true => eqblist t1 t2
      | false => false
      end
    end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'. rewrite <- eqb_refl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s as [| n s' IHs'].
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count : forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' IHs'].
  - simpl. reflexivity.
  - simpl. induction n. 
    + rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IHs'. reflexivity.
Qed.

(* count sum *)

Theorem minus_1_l : forall n : nat, n = S n - 1.
Proof.
  intros n. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem minus_0_l : forall n : nat, n = n - 0.
Proof.
  intros n. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem sum_app : forall (s1 s2 : bag),
  sum s1 s2 = s1 ++ s2.
Proof.
  intros s1 s2. induction s1 as [| n1 s1' IHs1'].
  + simpl. reflexivity.
  + simpl. rewrite <- IHs1'. reflexivity.
Qed.

Theorem bag_count_sum : forall (s1 s2 : bag) (n : nat),
  count n s1 + count n s2 = count n (sum s1 s2).
Proof.
  intros s1 s2 n. induction s1 as [| n1 s1' IHs1'].
  - simpl. reflexivity.
  - simpl. destruct (n =? n1) eqn:E.
    simpl. rewrite -> IHs1'. induction s2 as [| n2 s2' IHs2'].
      + rewrite -> app_nil_r. rewrite <- IHs1'. simpl. rewrite -> plus_comm. rewrite -> plus_O_n. reflexivity.
      + rewrite -> sum_app. reflexivity.
      + rewrite -> IHs1'. rewrite -> sum_app. reflexivity.
Qed.

Theorem rev_empty : rev [ ] = [ ].
Proof.
  simpl. reflexivity.
Qed.

Theorem rev_n : forall (n : nat), rev [n] = [n].
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem rev_empty_reverse : forall (l : natlist), [ ] = rev l -> [ ] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - intros H. rewrite <- rev_empty. rewrite -> H. rewrite -> rev_involutive. reflexivity.
Qed.

Theorem rev_empty_l : forall (l : natlist),
  rev [ ] = rev l -> [ ] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - intros H. rewrite <- rev_empty. rewrite <- rev_involutive. rewrite <- H. simpl. reflexivity.
Qed.

Theorem single_shot_rev : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H. induction l1 as [| n1 l1' IHl1'].
  - rewrite <- rev_empty. rewrite <- rev_empty_l.
    + rewrite -> rev_empty. reflexivity.
    + rewrite -> H. reflexivity.
  - induction l2 as [| n2 l2' IHl2'].
    + rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
    + rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
    | O => Some a
    | S n' => nth_error l' n'
    end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
    else nth_error' l' (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intros x. destruct x.
  simpl. rewrite <- eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => 
    if eqb_id x y
      then Some v
    else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. destruct d.
  - simpl. rewrite <- eqb_id_refl. reflexivity.
  - simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x v o. destruct d.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

End PartialMap.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).
(* 有'多少'个表达式具备类型 baz？ *)

(* 一个都没有 *)
(* 因为为了得到一个baz类型的值，我们需要把一个baz类型的值传递给x或y，
如果没有一个baz类型的值，我们就无法得到一个baz类型的值。
所以永远不可能创建出baz类型的值。 *)