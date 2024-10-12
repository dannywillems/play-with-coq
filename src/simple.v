Require Import Bool.
(* Require Import Arith. *)

Search bool.

(* SearchPattern bool. *)

Definition
  fp := nat.

Check
  and.

Check
  forall (x: nat) (y: nat), x + y = y + x.

Compute
  let f := fun x y => x + y in
  let g := fun x y => y + x in
  f 3 3 = g 3 4.

Definition
  weierstrass (a: fp) (b: fp) (x : fp) (y: fp) : fp := x * x * x + a * x + b - y * y.
