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

Check matrix.

(* Check matrix nat [1;2;3]. *)
(* Import VectorDef.VectorNotations. *)
(* Check [[[1;2;3]; [1;2;3]]]: matrix nat [1;2;3]. *)
(* Definition v1: Vector.t nat 3 := [1; 2; 3]. *)
(* Definition m1: matrix nat [2; 3]%list := [v1; v1]. *)
(* Compute [[m1]; [m1]]: matrix nat [2;1;2;3]%list. *)
(* Compute Fin.of_nat 0 2. *)
(* Compute Vector.nth [[m1]; [m1]] (Fin.F1). *)
(* Close Scope vector_scope. *)

(* TODO want to support
 * - index by a range, including the special range : meaning everything *)

(* Compute Fin.of_nat 2 3. *)
(* Check Vector.nth. *)

Definition product (dims: list nat) := List.fold_right Nat.mul 1 dims.

Fixpoint concat {A} {n m: nat} (v: Vector.t (Vector.t A m) n): Vector.t A (n * m) :=
  match v with
  | []%vector => []%vector
  | (x::xs)%vector => append x (concat xs)
  end.

(* Check List.concat. *)
(* Check @concat. *)
(* Compute concat m1. *)

Fixpoint linearize {A: Type} {dims: list nat}: matrix A dims -> matrix A [product dims] :=
  match dims with
  | [] => fun a => [a]%vector
  | head::tail => fun a => concat (Vector.map (linearize (dims := tail)) a)
  end.

(* Check @linearize. *)

(* Compute linearize ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector (1* : matrix nat [12] *1). *)

Definition nth {A: Type} {dims: list nat} (m: matrix A dims) (idx: nat): option A
  := match dims with
     | [] => None
     | _ =>
         let m' := linearize m
         in match Fin.of_nat (idx - 1) (product dims) with
            | inleft H => Some (Vector.nth m' H)
            | _ => None
            end
     end.

(* Compute List.map (λ n, nth ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector n) *)
(*                  [1;2;3;4;5;6;7;8;9;10;11;12]. *)

Fixpoint get {A: Type} {dims: list nat} (m: matrix A dims) (indexes: list nat): option A :=
  if Nat.eqb (length dims) (length indexes)
  then match dims, indexes return matrix A dims → option A with
       | [], [] => λ a, Some a
       | dimh::dimt, idxh::idxt => λ m',
           match Fin.of_nat (idxh - 1) dimh with
           | inleft H => @get A dimt (Vector.nth m' H) idxt
           | _ => None
           end
       | _, _ => λ _, None
       end m
  else None.

(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector []. *)
(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector [1]. *)
(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector [1;2]. *)
(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector [1;2;3]. *)
(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector [1;2;3;4;5]. *)
(* Compute get ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector [2;1;2;3]. *)

Inductive range: Type :=
  | Scalar: nat → range
  | Subrange: nat → nat → range
  | Fullrange.
