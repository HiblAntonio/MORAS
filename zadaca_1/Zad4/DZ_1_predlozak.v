Set Implicit Arguments.
Require Import List.
Import ListNotations.

(* Bit *)

Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : B) : B :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : B) : B :=
match x with
  | O => I
  | I => O
end.

Definition Add (x y c : B) : B :=
match x, y with
  | O, O => c
  | I, I => c
  | _, _ => Not c
end.

Definition Rem (x y c : B) : B :=
match x, y with
  | O, O => O
  | I, I => I
  | _, _ => c
end.

(* List *)

Fixpoint AndL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => And x y :: AndL xs ys
end.

Fixpoint OrL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Or x y :: OrL xs ys
end.

Fixpoint NotL (x : list B) : list B :=
match x with
  | [] => []
  | x :: xs => Not x :: NotL xs
end.

Fixpoint AddLr (x y : list B) (c : B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Add x y c :: AddLr xs ys (Rem x y c)
end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

Fixpoint IncLr (x : list B) (c : B) : list B :=
match x with
| [] => []
| x :: xs => Add x I c :: IncLr xs (Rem x I c)
end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* ALU *)

Definition flag_zx (f : B) (x : list B) : list B :=
match f with
| I => repeat O (length x)
| O => x
end.

Definition flag_nx (f : B) (x : list B) : list B :=
match f with
| I => NotL x
| O => x
end.

Definition flag_f (f : B) (x y : list B) : list B :=
match f with
| I => AddL x y
| O => AndL x y
end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B := 
  flag_nx no (flag_f f (flag_nx nx (flag_zx zx x)) (flag_nx ny (flag_zx zy y))).

(* Teoremi *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof. Abort.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof. Abort.

Lemma ALU_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O O = x.
Proof. Abort.

Lemma ALU_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O O = y.
Proof. Abort.

Lemma ALU_Not_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. Abort.

Lemma ALU_Not_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. Abort.

Lemma ALU_Add (x y : list B) : 
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. Abort.

(* DZ *)

Lemma ALU_And (x y : list B) : 
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof.
  now simpl.
Qed.

Lemma PL1 (l : list B): NotL(NotL l) = l.
Proof.
  induction l.
   - now reflexivity.
   - simpl. rewrite IHl. destruct a; now simpl.
Qed.

Lemma ALU_Or (x y : list B) : 
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof.
  intros.
  simpl.
  
  assert (PL1 : forall (l : list B), NotL(NotL l) = l).
  {
  induction l.
   - now reflexivity.
   - simpl. rewrite IHl. destruct a; now simpl.
  }
  
  assert(DoubleNeg : forall(a : B), Not (Not a) = a).
  {
    now destruct a. 
  }
  
  assert (DeMorgan : forall (a b : B), Not (And a b) = Or (Not a) (Not b)).
  {
    now destruct a, b.
  }

  assert (Final : forall (a b : list B), (OrL a b) = NotL(AndL (NotL a) (NotL b))).
  {
    intros a. induction a, b.
      1, 2, 3: now simpl.
      - simpl. rewrite !DeMorgan. rewrite !DoubleNeg. 
        f_equal. specialize (IHa b0). apply IHa.
  }

  now rewrite Final.
Qed.

Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
  intros H.
  destruct H, H0.
  simpl.
  rewrite H, H0.
 
  assert (H_NotL : forall (m : nat), NotL (repeat I m) = repeat O m).
  {
    intros m. induction m.
    try now simpl.
    simpl. 
    now rewrite IHm.
  }

  assert (H_NotL2 : forall (m : nat), NotL (repeat O m) = repeat I m).
  {
    intros m. induction m.
    try now simpl.
    simpl.
    now rewrite IHm.
  }

  rewrite ! H_NotL2. unfold AddL.

  assert (HRevL1 : forall (b : B) (m : nat), repeat b m ++ [b] = b :: repeat b m).
  {
    intros. induction m.
    try now simpl.
    simpl. now rewrite IHm.
  }
  
  assert (HRevL2 : forall (b : B) (m : nat), rev (repeat b m) = repeat b m).
  {
    intros. induction m.
    try now simpl.
    simpl. now rewrite IHm.
  }

  rewrite ! HRevL2.
 
  assert (HRevL3 : forall (b b1 : B) (m : nat), rev (b1 :: repeat b m) = rev (repeat b m) ++ [b1]).
  {
    now intros.
  }

  assert (Happ3 : forall (b b1 : B) (m : nat), NotL ((repeat b m) ++ [b1]) = (NotL (repeat b m)) ++ [(Not b1)]).
  {
    intros. induction m.
    now simpl.
    simpl. now f_equal.  
  }
  
  assert(HFH : forall (m : nat), AddLr (repeat I m) (repeat I m) I = repeat I m).
  {
   intros. induction m.
   now simpl.
   simpl. now f_equal.
  }
  
  assert(HFinal : forall(m : nat), (m <> 0) -> AddLr (repeat I m) (repeat I m) O = O :: (repeat I (Init.Nat.pred m))).
  {
    intros m. destruct m.
    now intros.
    intros. simpl. now f_equal. 
  }
  
  rewrite HFinal.
    - rewrite HRevL3. rewrite HRevL2. 
    rewrite ! Happ3. now rewrite H_NotL.
    - now simpl. 
Qed.







