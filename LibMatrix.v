Require Import Coq.Unicode.Utf8.
Require Export Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

(* only accepts even numbers of dimensions, and gets messy? *)
(* Definition matrix {A: Type} (rows cols: nat) := *)
(*   Vector.t (Vector.t A cols) rows. *)

Fixpoint matrix (A: Type) (dims: list nat) :=
  match dims with
  | [] => A
  | head::tail => Vector.t (matrix A tail) head
  end.

(* Check matrix. *)

(* Check matrix nat [1;2;3]. *)
(* Import VectorDef.VectorNotations. *)
(* Check [[[1;2;3]; [1;2;3]]]: matrix nat [1;2;3]. *)

Import VectorDef.VectorNotations.
Definition v1: Vector.t nat 3 := [1; 2; 3].
Definition m1: matrix nat [2; 3]%list := [v1; v1].
Compute [[m1]; [m1]]: matrix nat [2;1;2;3]%list.
Compute Fin.of_nat 0 2.
Compute Vector.nth [[m1]; [m1]] (Fin.F1).
Close Scope vector_scope.

(* want to support
 * - index by a single number? How does this work for non-vectors?
 * - by dimension
 * - index by a range, including the special range : meaning everything *)

(* Compute Fin.of_nat 2 3. *)
(* Check Vector.nth. *)

(* Definition product (dims: list nat) := List.fold_left Nat.mul dims 1. *)

(* Definition linearize {A: Type} {dims: list nat} (m: matrix A dims): matrix A [product dims]. *)
(* Proof. *)
(*   generalize dependent m. *)
(*   induction dims. *)
(*   - intros. *)
(*     assert (product [] = 1) by reflexivity. rewrite H; clear H. *)
(*     exact (Vector.cons A m 0 (Vector.nil A)). *)
(*   - intros. *)
(*     (1* why so hard? *1) *)
(*     assert (product (a::dims) = a * product dims). *)
(*     { unfold product. *)
(*       assert (a::dims = [a] ++ dims) by reflexivity. rewrite H; clear H. *)
(*       rewrite List.fold_left_app. *)
(*       assert (List.fold_left Nat.mul [a] 1 = a). admit. admit. } *)
(* Abort. *)

Compute @Vector.fold_left (list nat) (list nat) (@List.app nat) [] _ [[1]%list; [2]%list; [3]%list]%vector.

Definition linearize {A: Type} {dims: list nat} (m: matrix A dims): list A.
Proof.
  induction dims.
  - unfold matrix in m. apply [m].
  - simpl in m.
    apply (Vector.map IHdims) in m.
    apply (Vector.fold_left (@List.app A) [] m).
Defined.

(* Open Scope vector_scope. *)
(* Fixpoint linearize' {A: Type} {dims: list nat} (m: matrix A dims): list A := *)
(*   match m with *)
(*   | a => [a]%list *)
(*   | h::t => (@linearize' A (hd dims) h) ++ (Vector.map (@linearize' A tl dims) t) *)
(*   end. *)
(* Close Scope vector_scope. *)

(* Fixpoint linearize' {A: Type} {dims: list nat} (m: matrix A dims): list A := *)
(*   match dims with *)
(*   | [] => [] *)
(*   | h::t => Vector.fold_left *)
(*             (@app A) *)
(*             [] *)
(*             (Vector.map linearize' (m: Vector.t (matrix (list A) t) h)) *)
(*   end. *)

Compute linearize ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector.

Definition nth {A: Type} {dims: list nat} (m: matrix A dims) (idx: nat): option A
  := match dims with
     | [] => None
     | _ => List.nth_error (linearize m) (idx - 1)
     end.

Compute List.map (λ n, nth ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector n)
                 [1;2;3;4;5;6;7;8;9;10;11;12].
