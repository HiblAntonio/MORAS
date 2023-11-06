Set Implicit Arguments.
Require Import Setoid.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Bool.

Goal forall x y : bool,
  (x && negb y) || (negb x && negb y) || (negb x && y) = negb x || negb y.
Proof.
  now destruct x, y.
Qed.

Goal forall x y z : bool,
  negb(negb x && y && z) && negb(x && y && negb z) && (x && negb y && z) = x && negb y && z.
Proof.
  now destruct x, y, z.
Qed.