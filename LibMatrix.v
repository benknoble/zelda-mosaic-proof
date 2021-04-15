Require Import Coq.Unicode.Utf8.
Require Import microMatlab.LibTactics.
Require Import List.
Import ListNotations.
Require Import Lia.

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
  shape: list nat; (* A list of the dimensions for the matrix. *)
  contents: matrix_content A (* The elements of the matrix. *)
}.

(* Make the type arguments implicit for matrix. *)
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

(* Check that a matrix is well formed; i.e. the dimensions of the matrix match with the length of matrix contents. *)
Fixpoint well_formed' {A: Type} (shape: list nat) (contents: matrix_content A): Prop :=
  (* If the shape is an empty list, then the "matrix" in question must be a scalar. *)
  match shape with
  | [] => match contents with
          | Scalar _ => True
          | Matrix _ => False
          end
  (* Otherwise, we look at the head of the list and confirm that every element of this layer has the same length as the head. *)
  (* Then pass the tail to a new call of well_formed'.*)
  | h::t => match contents with
            | Matrix ms => length ms = h ∧ Forall (well_formed' t) ms
            | Scalar _ => False
            end
  end.

(* A restated version of well_formed that takes a matrix record as a parameter instead. *)
Definition well_formed {A: Type} (m: matrix A) := well_formed' (shape m) (contents m).
Hint Unfold well_formed: core.

(* A tactic used to repeatedly "unwind" a matrix's shape and contents to prove it is well-formed.*)
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

(* If a dimension of the shape list is 0, then the only matrix that can be represented is the empty matrix. *)
Theorem wf_0_vacuous: ∀ A t, @well_formed A {| shape := 0::t; contents := Matrix [] |}.
Proof. wf_easy. Qed.

(* The same well_formed definition as before, but written as Inductive Proposition instead. *)
Inductive well_formedI' {A: Type}: list nat → matrix_content A → Prop :=
  | WF_Scalar: ∀ a, well_formedI' [] (Scalar a)
  | WF_Empty: ∀ t, well_formedI' (0::t) (Matrix [])
  | WF_Cons: ∀ h t m ms,
      well_formedI' (h::t) (Matrix ms) →
      well_formedI' t m →
      well_formedI' ((S h)::t) (Matrix (m::ms))
.
(* Simple form of well_formedI' that only requires a matrix record to be passed as parameter. *)
Definition well_formedI {A: Type} (m: matrix A) := well_formedI' (shape m) (contents m).
Hint Unfold well_formedI: core.

(* Not entirely sure about this one. *)
(* I think it's saying - when given a shape t and list of matrix_content ms, if every matrix_content in ms matches shape t,
   you can construct a Matrix of ms, with the length of ms being prepended to the list of dimensions. *)
Theorem wfI_all_wf_t: ∀ A t (ms: list (matrix_content A)),
  Forall (well_formedI' t) ms →
  well_formedI' ((length ms)::t) (Matrix ms).
Proof.
  induction ms; intros; try constructor; inverts H; auto.
Qed.

(* Proof that both definitions of well_formed (boolean and IndProp version) are equivalent to one another. *)
Theorem well_formed_agree: ∀ A (m: matrix A), well_formed m ↔ well_formedI m.
Proof.
  destruct m as [shape contents].
  unfold well_formedI; unfold well_formed; simpl.
  split.
  - gen shape.
    mc_ind contents; intros shape Hwf; destruct shape; try easy; try constructor.
    inverts Hwf.
    apply wfI_all_wf_t.
    rewrite Forall_forall in *; auto.
  - intros.
    induction H; try wf_easy; simpl.
    inverts IHwell_formedI'1.
    split; auto.
Qed.

(* Similar as above but with only matrix content given as parameter. *)
Corollary well_formed'_agree: ∀ A (contents: matrix_content A) shape,
  well_formed' shape contents ↔ well_formedI' shape contents.
Proof.
  intros.
  specialize well_formed_agree with (m := {| shape := shape0; contents := contents0 |}).
  unfold well_formedI; unfold well_formed; simpl; auto.
Qed.


(* Given some matrix_content, this will compute the shape (dimensionality) of the matrix. *)
Fixpoint compute_shape {A: Type} (m: matrix_content A): list nat :=
  match m with
  | Scalar _ => []
  | Matrix [] => [0]
  | Matrix ((m::t) as ms) => (length ms)::(compute_shape m)
  end.

(* Compute compute_shape (Matrix [Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                                        Matrix [Scalar 4; Scalar 5; Scalar 6]]]). *)

(* If two matrices are well-formed and have the same shape, compute_shape will yield the same results for both. *)
Lemma wf_same_shape: ∀ A shape (m1 m2: matrix_content A),
  well_formed' shape m1 →
  well_formed' shape m2 →
  compute_shape m1 = compute_shape m2.
Proof.
  intros A shape.
  induction shape; destruct m1; destruct m2; try easy.
  intros.
  inverts H. inverts H0.
  destruct l; destruct l0; try easy.
  simpl. simpl in H. inverts H. f_equal.
  apply Forall_inv in H2, H1.
  apply IHshape; auto.
Qed.

(* If a matrix is well-formed and a list of matrix_content contains well-formed matrices of the same shape, then 
   compute_shape will have the same results for the matrix and for every matrix_content in the list. *)
Corollary wf_sub_same_shape: ∀ A shape (m: matrix_content A) (ms: list (matrix_content A)),
  well_formed' shape m →
  Forall (well_formed' shape) ms →
  Forall (λ m', compute_shape m' = compute_shape m) ms.
Proof.
  intros.
  apply Forall_impl with (well_formed' shape0); try assumption.
  intros. eapply wf_same_shape; eauto.
Qed.

(* Proof that if a matrix is well-formed, computing its shape with compute_shape will yield the same result as its existing shape. *)
Theorem compute_shape_wf_normalizes: ∀ A (m: matrix A),
  well_formed m →
  well_formed {| shape := compute_shape (contents m); contents := contents m |}.
Proof.
  destruct m as [shape contents]; simpl.
  gen shape.
  mc_ind contents; intros shape; destruct shape; try wf_easy; try easy.
  simpl. introv [Hlength Hms].
  destruct ms; try now wf_easy.
  simpl. split; try reflexivity.
  inverts Hms as Hm Hms.
  apply Forall_forall; introv HIn.
  rewrite Forall_forall in *.
  specialize H with (x := x).
  apply H with shape0 in HIn as Hwf; clear H.
  - replace (compute_shape m) with (compute_shape x); try assumption.
    clear Hwf.
    inverts HIn; auto.
    apply Hms in H.
    eapply wf_same_shape; eauto.
  - inverts HIn; auto.
Qed.

(* TODO want to support
 * - index by a range, including the special range ":" meaning everything *)

(* Check List.nth. *)
(* Check List.nth_error. *)

Definition product (shape: list nat) := List.fold_right Nat.mul 1 shape.

(* Check List.concat. *)

(* For a list of lists of length n, the length of all lists concatenated together is equal to n * the number of lists. *)
Theorem concat_length_mult: ∀ A (xss: list (list A)) n,
  Forall (λ xs, length xs = n) xss →
  length (concat xss) = n * length xss.
Proof.
  induction xss; intros.
  - simpl. lia.
  - simpl. inverts H.
    rewrite app_length.
    rewrite (IHxss (length a)); lia || assumption.
Qed.

(* Need a refresher for this one. *)
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
        inverts H. now inverts H1.
      + exists l. split; try reflexivity.
        inverts H.
        apply Forall_inv in H1.
        now inversion H1.
    * apply (IHms (h-1) n t).
      unfold well_formed; simpl.
      inverts H.
      split; try (simpl; lia).
      rewrite Forall_forall in H1. apply Forall_forall.
      intros. assert (In x (a::ms)) by (simpl; now right).
      clear H. apply H1 in H0. clear H1.
      destruct x; now inversion H0.
Qed.

(* Given a matrix of arbitrary dimensionality, will return a flat list of all the contents. *)
Fixpoint linearize' {A: Type} (contents: matrix_content A): list A :=
  match contents with
  | Scalar a => [a]
  | Matrix ms => flat_map linearize' ms
      (* equivalent to concat (map linearize' ms *)
      (* cf. flat_map_concat_map *)
  end.

(* Same as above, but lets us linearize when provided a matrix as parameter instead of matrix_content. *)
Definition linearize {A: Type} (m: matrix A): matrix A :=
  {| shape := [product (compute_shape (contents m))];
     contents := Matrix (map Scalar (linearize' (contents m))) |}.

(* Compute linearize {| shape := [1;2;3]; contents := Matrix [ *)
(*                 Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                         Matrix [Scalar 4; Scalar 5; Scalar 6]]]|}. *)

(* Proof that the length of a linearized matrix will be the same as the product of the matrix' dimensions. *)
Theorem linearize'_product: ∀ A (m: matrix A),
  well_formed m →
  length (linearize' (contents m)) = product (compute_shape (contents m)).
Proof.
  intros.
  rewrite well_formed_agree in H.
  destruct m as [shape contents]; unfold well_formedI in *; simpl in *.
  induction H; try reflexivity.
  simpl.
  rewrite app_length.
  replace (flat_map linearize' ms) with (linearize' (Matrix ms)) by reflexivity.
  rewrite IHwell_formedI'1.
  rewrite IHwell_formedI'2.
  f_equal.
  destruct ms; try reflexivity.
  simpl.
  inverts H.
  enough (compute_shape m = compute_shape m0).
  { now rewrite H. }
  rewrite <- well_formed'_agree in *.
  apply wf_same_shape with t; auto.
Qed.

(* Proof that if a matrix is well-formed, the linearized form of that matrix will also be well-formed. *)
Theorem linearize_wf: ∀ A (m: matrix A),
  well_formed m → well_formed (linearize m).
Proof.
  destruct m as [shape contents].
  unfold well_formed; simpl.
  induction contents; intros; destruct shape; try easy; try wf_easy.
  inverts H.
  rewrite Forall_forall in *.
  split.
  - rewrite map_length.
    pose ({| shape := (length l)::shape0; contents := Matrix l |}).
    replace (Matrix l) with (contents m); try reflexivity.
    apply linearize'_product.
    subst m. apply well_formed_agree.
    apply wfI_all_wf_t.
    apply Forall_forall in H1.
    apply Forall_impl with (well_formed' shape0); try assumption.
    intros. apply well_formed'_agree. assumption.
  - intros. rewrite in_map_iff in H. decompose record H; clear H.
    now subst.
Qed.

Definition nth {A: Type} (m: matrix A) (idx: nat): option A :=
  nth_error (linearize' (contents m)) idx.

(* Compute List.map (λ n, nth ([[m1]; [m1]]: matrix nat [2;1;2;3])%vector n) *)
(*                  [1;2;3;4;5;6;7;8;9;10;11;12]. *)

Inductive range: Type :=
  | Scalar: nat → range
  | Subrange: nat → nat → range
  | Fullrange.
