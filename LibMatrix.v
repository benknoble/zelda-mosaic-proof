Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.

Inductive matrix_content (A: Type) : Type :=
  | Scalar: A → matrix_content A
  | Matrix: list (matrix_content A) → matrix_content A
.

Arguments Scalar {A}.
Arguments Matrix {A} _.

(* Parameter P: matrix_content nat → Prop. *)
(* Parameter ms: list (matrix_content nat). *)
(* Parameter f: ∀ m: matrix_content nat, P m. *)
(* Check list_ind (Forall P) (Forall_nil P) (λ h t, Forall_cons h (f h)) ms. *)

Definition matrix_content_ind_strong:
  ∀ {A: Type} (P: matrix_content A → Prop),
  (∀ a: A, P (Scalar a)) →
  (∀ ms: list (matrix_content A), Forall P ms → P (Matrix ms)) →
  (∀ m: matrix_content A, P m)
  := λ A P PScalar PSubmatrix,
  fix f (m: matrix_content A)
  := match m with
     | Scalar a => PScalar a
     | Matrix ms => PSubmatrix ms (list_ind (Forall P) (Forall_nil P) (λ h t, Forall_cons h (f h)) ms)
     end.

Ltac mc_ind x := induction x using matrix_content_ind_strong.

(* Example mc_ind_ex: ∀ mc: matrix_content nat, *)
(*   match mc with *)
(*   | Scalar n => n ≥ 0 *)
(*   | Matrix ms => True (1* stating this part seems hard, so let's do something trivial *1) *)
(*   end. *)
(* Proof. *)
(*   mc_ind mc. *)
(*   (1* induction mc using matrix_content_ind_strong. *1) *)
(*   - apply le_0_n. *)
(*   - (1* induction hypothesis! *1) *)
(*     Check H. *)
(*     exact I. *)
(* Qed. *)

Record matrix (A: Type) : Type := {
  shape: list nat;
  contents: matrix_content A
}.

Arguments shape {A} _.
Arguments contents {A} _.

(* Check matrix. *)

(* Check {| shape := [1;2;3]; contents := Matrix [ *)
(*   Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*           Matrix [Scalar 4; Scalar 5; Scalar 6]]]|}. *)

(* Check List.Forall. *)
(* Check List.Forall_forall. *)
(* Check List.Forall_nth. *)
(* Check List.Forall_app. *)
(* Check List.Forall_elt. *)
(* Check List.Forall_rev. *)
(* (1* and a bunch more *1) *)

Fixpoint well_formed' {A: Type} (shape: list nat) (contents: matrix_content A): Prop :=
  match shape with
  | [] => match contents with
          | Scalar _ => True
          | Matrix _ => False
          end
  | h::t => match contents with
            | Matrix ms => length ms = h ∧ Forall (well_formed' t) ms
            | Scalar _ => False
            end
  end.

Definition well_formed {A: Type} (m: matrix A) := well_formed' (shape m) (contents m).

Hint Unfold well_formed: core.

Ltac wf_easy :=
  unfold well_formed;
  repeat (simpl; split; try reflexivity; (* simplify well_formed'/length, split the
                                            conjunct case, solve the length case *)
  apply Forall_forall; simpl; (* convert the Forall to In implies P, simplify In *)
  (let H := fresh "H" in intros x H; decompose sum H; clear H); (* destruct all the In cases *)
  subst (* use the hypothesis to simplify the match arms, which either gets us
  another well_formed' invocation (repeat!) or a "True", which (accidentally)
  gets handled by the split near the top *)).

Example wf_1: well_formed {| shape := [1;2;3]; contents := Matrix [
                Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3];
                        Matrix [Scalar 4; Scalar 5; Scalar 6]]] |}.
Proof.
  wf_easy.

  (* (1* old tedious proof *1) *)
  (* unfold well_formed. *)
  (* simpl; split; try reflexivity. *)
  (* apply Forall_forall; simpl. intros x [H | []]; subst. *)
  (* simpl; split; try reflexivity. *)
  (* apply Forall_forall; simpl. intros x [H | [H | []]]; subst. *)
  (* all: simpl; split; try reflexivity. *)
  (* all: apply Forall_forall; simpl. *)
  (* all: intros x [H | [H | [H | []]]]; now subst x. *)
Qed.

Theorem wf_0_broken: ∀ t, @well_formed nat {| shape := 0::t; contents := Matrix [] |}.
Proof. wf_easy. Qed.

Fixpoint compute_shape {A: Type} (m: matrix_content A): list nat :=
  match m with
  | Scalar _ => []
  | Matrix [] => [0]
  | Matrix ((m::t) as ms) => (length ms)::(compute_shape m)
  end.

(* Compute compute_shape (Matrix [Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                                        Matrix [Scalar 4; Scalar 5; Scalar 6]]]). *)

(* Theorem compute_shape_wf_correct: ∀ A (m: matrix A), *)
(*   well_formed m → *)
(*   compute_shape (contents m) = shape m. *)
(* Proof. *)
(*   intros. destruct m as [shape contents]; simpl. *)
(*   induction contents; destruct shape; try now inversion H. *)
(*   destruct l; inversion H; subst. *)
(*   - simpl in *. (1* shape0 can be anything! see wf_2 *1) *)
(* Abort. *)

Lemma wf_sub_same_shape: ∀ A shape (m: matrix_content A) (ms: list (matrix_content A)),
  well_formed' shape m →
  Forall (well_formed' shape) ms →
  Forall (λ m', compute_shape m' = compute_shape m) ms.
Proof.
Admitted.

Theorem compute_shape_wf_normalizes: ∀ A (m: matrix A),
  well_formed m →
  well_formed {| shape := compute_shape (contents m); contents := contents m |}.
Proof.
  destruct m as [shape contents]; simpl.
  generalize dependent shape.
  mc_ind contents; intros shape; destruct shape; try wf_easy; try easy.
  simpl. intros [].
  destruct ms; try now wf_easy.
  simpl. split; try reflexivity.
  inversion H1; subst; clear H1.
  apply Forall_forall; intros.
  rewrite Forall_forall in H.
  specialize H with (x := x).
  assert (In x (m::ms)) by auto.
  apply H with shape0 in H0; clear H.
  all: cycle 1.
  - inversion H0; subst; clear H0; try assumption.
    rewrite Forall_forall in H5; auto.
  - replace (compute_shape m) with (compute_shape x); try assumption.
    clear H0.
    inversion H1; subst; clear H1; try reflexivity.
    apply wf_sub_same_shape with (ms := ms) in H4; try assumption.
    rewrite Forall_forall in H4; auto.
Qed.

(* TODO want to support
 * - index by a range, including the special range ":" meaning everything *)

(* Check List.nth. *)
(* Check List.nth_error. *)

Definition product (shape: list nat) := List.fold_right Nat.mul 1 shape.

(* Check List.concat. *)

Require Import Lia.

Theorem concat_length_mult: ∀ A (xss: list (list A)) n,
  Forall (λ xs, length xs = n) xss →
  length (concat xss) = n * length xss.
Proof.
  induction xss; intros.
  - simpl. lia.
  - simpl. inversion H; subst.
    rewrite app_length.
    rewrite (IHxss (length a)); lia || assumption.
Qed.

Theorem wf_all_length_same: ∀ A (ms: list (matrix_content A)) h n t,
  well_formed {| shape := h::n::t; contents := Matrix ms |} →
  Forall (λ m', ∃ ms', m' = Matrix ms' ∧ length ms' = n) ms.
Proof.
  induction ms.
  - (* the conclusion is vacuously true *)
    intros. apply Forall_nil.
  - intros. apply Forall_cons.
    * clear IHms. destruct a.
      + (* contradiction: no-longer well-formed *)
        inversion H; clear H; clear H0.
        now inversion H1.
      + exists l. split; try reflexivity.
        inversion H; clear H0; clear H.
        apply Forall_inv in H1.
        now inversion H1.
    * apply (IHms (h-1) n t).
      unfold well_formed; simpl.
      inversion H; clear H.
      split.
      + simpl in H0; lia.
      + clear H0. rewrite Forall_forall in H1. apply Forall_forall.
        intros. assert (In x (a::ms)) by (simpl; now right).
        clear H. apply H1 in H0. clear H1.
        destruct x; now inversion H0.
Qed.

Fixpoint linearize' {A: Type} (contents: matrix_content A): list A :=
  match contents with
  | Scalar a => [a]
  | Matrix ms => flat_map linearize' ms
      (* equivalent to concat (map linearize' ms *)
      (* cf. flat_map_concat_map *)
  end.

Definition linearize {A: Type} (m: matrix A): matrix A :=
  {| shape := [product (compute_shape (contents m))];
     contents := Matrix (map Scalar (linearize' (contents m))) |}.

(* Compute linearize {| shape := [1;2;3]; contents := Matrix [ *)
(*                 Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                         Matrix [Scalar 4; Scalar 5; Scalar 6]]]|}. *)

Theorem linearize'_product: ∀ A (m: matrix_content A),
  length (linearize' m) = product (compute_shape m).
Proof.
  (* (1* stuff from an old proof that might be relevant *1) *)
  (*     destruct shape0. *)
  (*     + inversion H1; subst; try reflexivity. *)
  (*       destruct x. *)
  (*       -- simpl. admit. (1* induction l needed *1) *)
  (*       -- destruct H0. *)
  (*     + simpl. rewrite PeanoNat.Nat.mul_assoc. *)
  (*       apply wf_all_length_same in H. *)
  (*       rewrite (concat_length_mult _ _ n). *)
  (*       -- rewrite (PeanoNat.Nat.mul_comm _ n). *)
  (*          admit. (1* induction? length (map linearize' l) = length * product shape0 *1) *)
  (*       -- (1* need relationship with produce, linearize', length? *1) *)
Admitted.

Theorem linearize_wf: ∀ A (m: matrix A),
  well_formed m → well_formed (linearize m).
Proof.
  intros. destruct m as [shape contents].
  induction contents; destruct shape; try now inversion H.
  - clear H.
    unfold linearize; simpl.
    wf_easy.
  - inversion H; subst.
    unfold linearize. rewrite <- linearize'_product. simpl.
    unfold well_formed; simpl; split.
    * now rewrite map_length.
    * apply Forall_forall; intros.
      rewrite in_map_iff in H0. decompose record H0; clear H0.
      now subst.
Qed.

Definition nth {A: Type} (m: matrix A) (idx: nat): option A :=
  nth_error (linearize' (contents m)) idx.

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
