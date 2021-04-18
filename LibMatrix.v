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

Theorem wf_0_vacuous: ∀ A t, @well_formed A {| shape := 0::t; contents := Matrix [] |}.
Proof. wf_easy. Qed.

Inductive well_formedI' {A: Type}: list nat → matrix_content A → Prop :=
  | WF_Scalar: ∀ a, well_formedI' [] (Scalar a)
  | WF_Empty: ∀ t, well_formedI' (0::t) (Matrix [])
  | WF_Cons: ∀ h t m ms,
      well_formedI' (h::t) (Matrix ms) →
      well_formedI' t m →
      well_formedI' ((S h)::t) (Matrix (m::ms))
.

Definition well_formedI {A: Type} (m: matrix A) := well_formedI' (shape m) (contents m).
Hint Unfold well_formedI: core.

Theorem wfI_all_wf_t: ∀ A t (ms: list (matrix_content A)),
  Forall (well_formedI' t) ms →
  well_formedI' ((length ms)::t) (Matrix ms).
Proof.
  induction ms; intros; try constructor; inverts H; auto.
Qed.

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

Corollary well_formed'_agree: ∀ A (contents: matrix_content A) shape,
  well_formed' shape contents ↔ well_formedI' shape contents.
Proof.
  intros.
  specialize well_formed_agree with (m := {| shape := shape0; contents := contents0 |}).
  unfold well_formedI; unfold well_formed; simpl; auto.
Qed.

Fixpoint compute_shape {A: Type} (m: matrix_content A): list nat :=
  match m with
  | Scalar _ => []
  | Matrix [] => [0]
  | Matrix ((m::t) as ms) => (length ms)::(compute_shape m)
  end.

(* Compute compute_shape (Matrix [Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                                        Matrix [Scalar 4; Scalar 5; Scalar 6]]]). *)

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

Corollary wf_sub_same_shape: ∀ A shape (m: matrix_content A) (ms: list (matrix_content A)),
  well_formed' shape m →
  Forall (well_formed' shape) ms →
  Forall (λ m', compute_shape m' = compute_shape m) ms.
Proof.
  intros.
  apply Forall_impl with (well_formed' shape0); try assumption.
  intros. eapply wf_same_shape; eauto.
Qed.

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
  nth_error (linearize' (contents m)) (idx-1).

(* what about 0? 0-1 = 0… *)
(* Compute List.map (nth {| shape := [1;2;3]; contents := Matrix [ *)
(*                 Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                         Matrix [Scalar 4; Scalar 5; Scalar 6]]] |}) *)
(*                  [1;2;3;4;5;6;7]. *)

Fixpoint list_option_to_option_list {A: Type} (xs: list (option A)): option (list A)
  := match xs with
     | [] => Some []
     | None::_ => None
     | Some x::t => match list_option_to_option_list t with
                    | None => None
                    | Some t => Some (x::t)
                    end
     end.

Theorem list_option_to_option_list_none_iff_contains_none: ∀ A (xs: list (option A)),
  list_option_to_option_list xs = None ↔ In None xs.
Proof.
  induction xs; try easy.
  destruct a; simpl; split; try (intros; auto).
  - destruct (list_option_to_option_list xs); try easy.
    right. now apply IHxs.
  - destruct H; try discriminate.
    apply IHxs in H.
    now rewrite H.
Qed.

Theorem list_option_to_option_list_some_iff_all_some: ∀ A (xs: list (option A)) xs',
  list_option_to_option_list xs = Some xs'
  ↔
  (length xs = length xs'
  ∧ ∀ i,
  match List.nth_error xs i with
    (* out of bounds *)
  | None => List.nth_error xs' i = None
    (* should be no None in xs *)
  | Some None => False
    (* lists agree in bounds *)
  | Some (Some x) => List.nth_error xs' i = Some x
  end).
Proof.
  induction xs; destruct xs'; split; intros; try easy.
  - split; try reflexivity. now destruct i.
  - destruct a; simpl in H; destruct (list_option_to_option_list xs); try easy.
  - specialize IHxs with xs'.
    destruct a; simpl in H; destruct (list_option_to_option_list xs); try easy.
    inverts H.
    assert (Some xs' = Some xs') by auto.
    apply IHxs in H; clear IHxs. destruct H.
    split.
    * simpl. now f_equal.
    * destruct i; try easy. simpl. gen i. auto.
  - specialize IHxs with xs'.
    destruct H.
    inverts H.
    destruct a; simpl.
    * destruct (list_option_to_option_list xs).
      + f_equal.
        assert (a = a0).
        { specialize H0 with 0. simpl in H0. now inverts H0. }
        subst. f_equal.
        enough (Some l = Some xs'). { now inverts H. }
        apply IHxs; clear IHxs.
        split; try easy.
        intros. now specialize H0 with (1+i).
      + enough (None = Some xs') by easy.
        apply IHxs; clear IHxs.
        split; try easy.
        intros. now specialize H0 with (1+i).
    * now specialize H0 with 0.
Qed.

Inductive range: Type :=
  | Scalar: nat → range
  | Subrange: nat → nat → range
  | Fullrange.
