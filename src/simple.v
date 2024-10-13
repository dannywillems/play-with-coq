Require Import Bool.
Require Import Arith String.

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

(** Define a simple polynomial expression.
    Its type is a set. We can build a constant expression from a natural number,
    or we can add or multiply two expressions.

    The first keyword is Inductive because it is an inductive definition, i.e.
    some constructors depend on the type itself.
 *)
Inductive expression: Set :=
| Constant: nat -> expression
| Plus: expression -> expression -> expression
| Times: expression -> expression -> expression.

(** Evaluate the expression as a natural.
    It is a recursive function, and Coq uses the keyword Fixpoint for recursive
    functions.
    This example shows how to destruct an inductive type.
    The syntax is pretty common.
    Note that we always end a statement with a dot!
 *)
Fixpoint eval (e: expression) : nat :=
  match e with
  | Constant n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Times e1 e2 => eval e1 * eval e2
  end.
