Require Import Coq.Unicode.Utf8.
Require Import microMatlab.LibTactics.
Require Import List.
Import ListNotations.
Require Import Lia.

(** [matrix_content] contains the contents of the matrix in a tagged structure *)
Inductive matrix_content (A: Type) : Type :=
  | Scalar: A → matrix_content A
  | Matrix: list (matrix_content A) → matrix_content A
.

(** with an implicit type argument. *)
Arguments Scalar {A}.
Arguments Matrix {A} _.

(* Parameter P: matrix_content nat → Prop. *)
(* Parameter ms: list (matrix_content nat). *)
(* Parameter f: ∀ m: matrix_content nat, P m. *)
(* Check list_ind (Forall P) (Forall_nil P) (λ h t, Forall_cons h (f h)) ms. *)

(** An induction principle for [matrix_content] that also gives information
 * about the submatrices. This can be used for a proof by induction, but choose
 * the induction hypothesis carefully! *)
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

(** A tactic that makes induction using [matrix_content_ind_strong] shorter to
 * invoke. *)
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


(** The actual matrix type. *)
Record matrix (A: Type) : Type := {
  shape: list nat; (* A list of the dimensions for the matrix. *)
  contents: matrix_content A (* The elements of the matrix. *)
}.

(** Implicit type arguments for matrix. *)
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

(** "Check" by computing a proposition (i.e., proof burdern) that a [matrix] is
 * well formed; i.e. the dimensions of the matrix match with the length of
 * matrix contents. A scalar has empty [shape]. *)
Fixpoint well_formed' {A: Type} (shape: list nat) (contents: matrix_content A): Prop :=
  (* If the [shape] is an empty list, then the [matrix] in question must be a
   * [Scalar]. *)
  match shape with
  | [] => match contents with
          | Scalar _ => True
          | Matrix _ => False
          end
  (* Otherwise, we look at the [matrix_content] and make sure it has the same
   * length as the head of the dimensions list.
   * Then pass the tail to a new call of [well_formed'].*)
  | h::t => match contents with
            | Matrix ms => length ms = h ∧ Forall (well_formed' t) ms
            | Scalar _ => False
            end
  end.

(** A restated version of [well_formed'] that takes a [matrix] record as a
 * parameter instead. This is more convenient then unbundling the matrix in some
 * cases.*)
Definition well_formed {A: Type} (m: matrix A) := well_formed' (shape m) (contents m).
Hint Unfold well_formed: core.

(** A tactic used to repeatedly "unwind" a matrix's shape and contents to prove
 * it is well-formed. Handles most "literal"/"ground" cases automatically. *)
Ltac wf_easy :=
  unfold well_formed;
  repeat (simpl; split; try reflexivity; (* simplify well_formed'/length, split the
                                            conjunct case, solve the length case *)
  apply Forall_forall; simpl; (* convert the Forall to In implies P, simplify In *)
  (let H := fresh "H" in intros x H; decompose sum H; clear H); (* destruct all the In cases *)
  subst (* use the hypothesis to simplify the match arms, which either gets us
  another well_formed' invocation (repeat!) or a "True", which (accidentally)
  gets handled by the split near the top *)).

(* Application of the wf_easy tactic to show that a 3-dimensional matrix is well-formed. *)
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

(** If a dimension of the shape list is 0, then the only matrix that can be
 * represented is the empty matrix. *)
Theorem wf_0_vacuous: ∀ A t, @well_formed A {| shape := 0::t; contents := Matrix [] |}.
Proof. wf_easy. Qed.

(** The same [well_formed'] definition as before, but written as Inductive
 * Proposition instead. This make it possible to perform induction on evidence;
 * i.e., induction on a matrix in an expected way (given that the matrix is
 * [well_formedI']). *)
Inductive well_formedI' {A: Type}: list nat → matrix_content A → Prop :=
  | WF_Scalar: ∀ a, well_formedI' [] (Scalar a)
  | WF_Empty: ∀ t, well_formedI' (0::t) (Matrix [])
  | WF_Cons: ∀ h t m ms,
      well_formedI' (h::t) (Matrix ms) →
      well_formedI' t m →
      well_formedI' ((S h)::t) (Matrix (m::ms))
.

(** Simple form of [well_formedI'] that only requires a matrix record to be
 * passed as parameter and unwraps it to get its shape and contents. Analogous
 * to [well_formed]. *)
Definition well_formedI {A: Type} (m: matrix A) := well_formedI' (shape m) (contents m).
Hint Unfold well_formedI: core.

(** When given a [shape] [t] and list of [matrix_content] [ms], if every
 * [matrix_content] in [ms] matches [shape] [t], you can construct a
 * [well_formedI'] [Matrix] of [ms], with the length of [ms] being prepended to
 * the list of dimensions. *)
Theorem wfI_all_wf_t: ∀ A t (ms: list (matrix_content A)),
  Forall (well_formedI' t) ms →
  well_formedI' ((length ms)::t) (Matrix ms).
Proof.
  (* induction on the list *)
  induction ms; intros;
  (* the base case is the constructor WF_Empty *)
  constructor;
  (* the inductive case is an instance of WF_Cons, leaving two subgoals. *)
  inverts H;
  (* but the hypothesis provides enough information (combined with the induction
   * hypothesis) to finish the proof. *)
  (* - apply IHms. assumption. *)
  (* - assumption. *)
  auto.
Qed.

(** Proof that both definitions of [well_formed] (boolean and IndProp version)
 * are equivalent to one another. Uses [wfI_all_wf_t] to demonstrate matching
 * shape across both definitions. *)
Theorem well_formed_agree: ∀ A (m: matrix A), well_formed m ↔ well_formedI m.
Proof.
  (* need to discuss specific parts of matrix, esp. for induction to work *)
  destruct m as [shape contents].
  unfold well_formedI; unfold well_formed; simpl.
  split.
  - (* well_formed m → well_formedI m *)
    (* induction on the contents, but with shape crucially generalized *)
    gen shape.
    mc_ind contents; intros shape Hwf;
      (* need case analysis on shape to keep in sync with contents *)
      destruct shape;
      (* but, some cases are trivial (base cases) and others are contradictory *)
      try easy;
      (* and try constructors from well_formedI' on the rest *)
      try constructor.
    (* well_formed' (n::shape) (Matrix ms) → well_formedI' (n::shape) (Matrix ms) *)
    inverts Hwf. (* use the information we know *)
    apply wfI_all_wf_t.
    (* just need to connect all the pieces via the induction hypothesis;
     * Forall_impl could probably do it, but unfolding the Foralls gives enough
     * to put the pieces together *)
    rewrite Forall_forall in *; auto.
  - (* well_formedI m → well_formed m *)
    intros.
    (* induction on the evidence *)
    induction H;
      (* wf_easy takes care of the base-cases *)
      try wf_easy; simpl.
    (* well_formedI' ((S h)::t) Matrix (m::ms) → well_formed' ((S h)::t) (Matrix (m::ms) *)
    (* use what we know *) inverts IHwell_formedI'1.
    (* all the pieces are there, go find them *)
    split; auto.
Qed.

(** Similar as [well_formed_agree] but for the unwrapped [well_formed'] instead.
 * A more natural way would have been to prove this first, and do the other
 * version as a corollary; yet we initially stated the first agreement, and only
 * later realized we needed this one. *)
Corollary well_formed'_agree: ∀ A (contents: matrix_content A) shape,
  well_formed' shape contents ↔ well_formedI' shape contents.
Proof.
  intros.
  (* introduce the previous theorem *)
  specialize well_formed_agree with (m := {| shape := shape0; contents := contents0 |}).
  (* which is exactly enough *)
  (* intros; assumption. *)
  auto.
Qed.

(** Given some [matrix_content], this will compute the shape (dimensionality) of
 * the matrix. The result is somewhat "normalized," as the empty matrix is given
 * shape [0] (when we have already proved it is well-formed for *any* shape
 * 0::t). *)
Fixpoint compute_shape {A: Type} (m: matrix_content A): list nat :=
  match m with
  | Scalar _ => []
  | Matrix [] => [0]
  | Matrix ((m::t) as ms) => (length ms)::(compute_shape m)
  end.

(* Compute compute_shape (Matrix [Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                                        Matrix [Scalar 4; Scalar 5; Scalar 6]]]). *)

(** If two matrices are well-formed and have the same shape, [compute_shape] will
 * yield the same results for both. *)
Lemma wf_same_shape: ∀ A shape (m1 m2: matrix_content A),
  well_formed' shape m1 →
  well_formed' shape m2 →
  compute_shape m1 = compute_shape m2.
Proof.
  intros A shape.
  (* induction on the shape list *)
  induction shape;
    (* case analysis to keep in sync *)
    destruct m1, m2;
    (* get rid of the base/contradictory cases *)
    try easy.
  intros.
  (* use what we know *) inverts H. inverts H0.
  (* we need information about the actual lists to simplify compute_shape *)
  destruct l; destruct l0; try easy.
  (* related m to m0 and l to l0 *)
  simpl. simpl in H. inverts H.
  (* l0 gone *) f_equal.
  (* extract heads *) apply Forall_inv in H2, H1.
  (* the induction hypothesis combines with other assumptions to finish it *)
  auto.
Qed.

(** Extension of [wf_same_shape] to lists. *)
Corollary wf_sub_same_shape: ∀ A shape (m: matrix_content A) (ms: list (matrix_content A)),
  well_formed' shape m →
  Forall (well_formed' shape) ms →
  Forall (λ m', compute_shape m' = compute_shape m) ms.
Proof.
  intros.
  (* previous gives well_formed' shape0 → equivalent compute_shapes; Forall_impl
  * lifts the implication to lists. *)
  apply Forall_impl with (well_formed' shape0); try assumption.
  intros.
  (* conclusions match; eapply/eauto necessary to find shape0 *)
  (* apply wf_same_shape with shape0; auto. *)
  eapply wf_same_shape; eauto.
Qed.

(** Proof that if a matrix is well-formed, the matrix formed by its content and
 * the computed shape of its contents will also be well-formed. *)
Theorem compute_shape_wf_normalizes: ∀ A (m: matrix A),
  well_formed m →
  well_formed {| shape := compute_shape (contents m); contents := contents m |}.
Proof.
  destruct m as [shape contents]; simpl.
  (* induction on the contents; generalized shape necessary *)
  gen shape.
  mc_ind contents;
    (* usual case analysis *)
    intros shape; destruct shape; try wf_easy; try easy.
  (* inductive case *)
  simpl. introv [Hlength Hms].
  (* case analsysis on ms to handle match; see if wf_easy is enough to finish *)
  destruct ms; try now wf_easy.
  (* unfold definition; get to the interesting bit *)
  simpl. split; try reflexivity.
  (* change some forms to the usual quantifiers; the goal is to use the
  * induction hypothesis H *)
  inverts Hms as Hm Hms.
  rewrite Forall_forall in *.
  introv HIn.
  specialize H with (x := x).
  (* now apply it, but we have to keep the HIn around, hence as
   * apply H in HIn doesn't work (cannot find shape?), instead of giving a ∀
   * shape *)
  apply H with shape0 in HIn as Hwf; clear H.
  - (* original goal: well_formed' (compute_shape m) x
     * but we know well_formed' (compute_shape x) x; can we connect them? cf.
     * Hms and Hin combined with wf_same_shape. *)
    replace (compute_shape m) with (compute_shape x); try assumption.
    clear Hwf.
    inverts HIn; auto. (* auto handles the x = m case, which is reflexive *)
    apply Hms in H.
    (* Hms and H will are enough for wf_same_shape *)
    eapply wf_same_shape; eauto.
  - (* premise of the original induction hypothesis needed for application
     * just like earlier, HIn/Hms are enough to finish it *)
    inverts HIn; auto.
Qed.

(* TODO want to support
 * - index by a range, including the special range ":" meaning everything *)

(* Check List.nth. *)
(* Check List.nth_error. *)

Definition product (shape: list nat) := List.fold_right Nat.mul 1 shape.

(* Check List.concat. *)

(** For a list of lists of length n, the length of all lists concatenated
 * together is equal to n * the number of lists. *)
Theorem concat_length_mult: ∀ A (xss: list (list A)) n,
  Forall (λ xs, length xs = n) xss →
  length (concat xss) = n * length xss.
Proof.
  induction xss; intros.
  - (* [] *)
    simpl. lia.
  - (* a::xss *)
    simpl. inverts H.
    rewrite app_length.
    (* finish with the induction hypothesis *)
    rewrite (IHxss (length a));
      (* by lia, for the original goal *)
      lia
      (* or assumption for the premise *)
      || assumption.
Qed.

(* Maybe not necessary? *)
(** Attempt to relate well-formedness to [concat_length_mult] *)
Theorem wf_all_length_same: ∀ A (ms: list (matrix_content A)) h n t,
  well_formed {| shape := h::n::t; contents := Matrix ms |} →
  Forall (λ m', ∃ ms', m' = Matrix ms' ∧ length ms' = n) ms.
Proof.
  induction ms; intros;
    (* handles [], sets up goals for a::ms *)
    try constructor.
  (* a::ms *)
  - (* P a *)
    clear IHms. destruct a.
    * (* Scalar; contradiction: no-longer well-formed *)
      inverts H. now inverts H1.
    * (* Matrix *)
      exists l. split; try reflexivity.
      inverts H.
      apply Forall_inv in H1.
      now inverts H1.
  - (* Forall P l *)
    (* notice the (h-1), since h is for Matrix (a::ms) and we need ms here *)
    apply (IHms (h-1) n t).
    unfold well_formed; simpl.
    inverts H.
    split; try (simpl; lia).
    (* massaging the Foralls *)
    rewrite Forall_forall in *.
    intros.
    (* easy premise for H1, which is well-formedness on submatrices *)
    assert (In x (a::ms)) by (simpl; now right). clear H.
    apply H1 in H0. clear H1.
    (* one contradiction, one easy *)
    destruct x; now inversion H0.
Qed.

(** Given a matrix of arbitrary dimensionality, will return a flat list of all
 * the contents. *)
Fixpoint linearize' {A: Type} (contents: matrix_content A): list A :=
  match contents with
  | Scalar a => [a]
  | Matrix ms => flat_map linearize' ms
      (* equivalent to concat (map linearize' ms *)
      (* cf. flat_map_concat_map *)
  end.

(** Same as [linearize'], but with a [matrix] record directly. *)
Definition linearize {A: Type} (m: matrix A): matrix A :=
  {| shape := [product (compute_shape (contents m))];
     contents := Matrix (map Scalar (linearize' (contents m))) |}.

(* Compute linearize {| shape := [1;2;3]; contents := Matrix [ *)
(*                 Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                         Matrix [Scalar 4; Scalar 5; Scalar 6]]]|}. *)

(** Proof that the length of a linearized matrix will be the same as the product
 * of the matrix's dimensions. Part of the spec of [linearize]. *)
Theorem linearize'_product: ∀ A (m: matrix A),
  well_formed m →
  length (linearize' (contents m)) = product (compute_shape (contents m)).
Proof.
  intros.
  (* let's use the inductive version for better information *)
  rewrite well_formed_agree in H.
  destruct m as [shape contents]; unfold well_formedI in *; simpl in *.
  induction H; (* base cases *) try reflexivity.
  (* inductive case *)
  simpl.
  rewrite app_length.
  (* definition of linearize' on a Matrix *)
  replace (flat_map linearize' ms) with (linearize' (Matrix ms)) by reflexivity.
  rewrite IHwell_formedI'1; clear IHwell_formedI'1.
  rewrite IHwell_formedI'2; clear IHwell_formedI'2.
  (* only need equality for one more set of addends *) f_equal.
  (* depends on length of ms *)
  destruct ms; (* [] *) try reflexivity.
  (* m0::ms *)
  simpl. inverts H.
  (* just need (compute_shape m = compute_shape m0) *)
  enough (compute_shape m = compute_shape m0). { now rewrite H. }
  (* but wf_same_shape will do it, if we use the non-I versions *)
  rewrite <- well_formed'_agree in *.
  apply wf_same_shape with t; auto.
Qed.

(** Proof that if a matrix is well-formed, the linearized form of that matrix
 * will also be well-formed. Part of the spec of [linearize]. *)
Theorem linearize_wf: ∀ A (m: matrix A),
  well_formed m → well_formed (linearize m).
Proof.
  destruct m as [shape contents].
  unfold well_formed; simpl.
  (* regular contents induction is enough; do the usual syncing on shape/get rid
  * of easy/contradictory cases *)
  induction contents; intros; destruct shape; try easy; try wf_easy.
  inverts H.
  (* usual quantifiers *)
  rewrite Forall_forall in *.
  split.
  - (* length … = product … *)
    rewrite map_length.
    (* re-shape for linearize'_product *)
    pose ({| shape := (length l)::shape0; contents := Matrix l |}).
    replace (Matrix l) with (contents m); try reflexivity.
    apply linearize'_product.
    (* now go back and use the details of the matrix, but in the inducrive
     * version, since we can relate the use of length to it more easily *)
    subst m. apply well_formed_agree.
    apply wfI_all_wf_t.
    (* back to Forall *)
    apply Forall_forall in H1.
    (* P implies Q under Forall *)
    apply Forall_impl with (well_formed' shape0); try assumption.
    intros. apply well_formed'_agree. assumption.
  - (* everyting is scalar in the map, since the shape list can only be a single
     * element after linearize. but since the function being mapped is the
     * Scalar constructor, this should be easy. *)
    intros. rewrite in_map_iff in H. decompose record H; clear H.
    now subst.
Qed.

(** Given a matrix, will return the nth element of the matrix after linearizing.
 * [n] will work for values between 1 and the product of the matrix's shape. *)
Definition nth {A: Type} (m: matrix A) (idx: nat): option A :=
  nth_error (linearize' (contents m)) (idx-1).

(* what about 0? 0-1 = 0… *)
(* Compute List.map (nth {| shape := [1;2;3]; contents := Matrix [ *)
(*                 Matrix [Matrix [Scalar 1; Scalar 2; Scalar 3]; *)
(*                         Matrix [Scalar 4; Scalar 5; Scalar 6]]] |}) *)
(*                  [1;2;3;4;5;6;7]. *)

(* TODO spec nth *)

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
  induction xs; (* [] *) try easy.
  (* a::xs
   * to proceed depends on whether a is None or Some
   * some of the ↔ cases are easy *)
  destruct a; simpl; split; try (intros; auto).
  - (* list_option_to_option_list (Some a::xs) = None → In None (Some a::xs) *)
    (* analysis required by definition, but one case is contradictory *)
    destruct (list_option_to_option_list xs); try easy.
    (* but now the induction hypothesis applies *)
    right. now apply IHxs.
  - (* In None (Some a::xs) → list_option_to_option_list (Some a::xs) = None *)
    (* must be the case that None is in xs *)
    destruct H; try discriminate.
    (* but then the induction hypothesis applies *)
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
  (* induction on xs but with xs' in sync; get rid of all the
   * contradictions, and split the ↔ proofs *)
  induction xs; destruct xs'; split; intros; try easy.
  - (* list_option_to_option_list [] = Some [] → … *)
    split; try reflexivity.
    (* nth_error always None on the empty lists *) now destruct i.
  - (* list_option_to_option_list (a::xs) = Some [] → … *)
    (* spot the contradiction in H ^ *)
    destruct a; simpl in H; destruct (list_option_to_option_list xs); try easy.
  - (* list_option_to_option_list (a::xs) = Some (a0::xs') → … *)
    (* really only care about xs' *)
    specialize IHxs with xs'.
    (* usualy analysis on a/xs *)
    destruct a; simpl in H; destruct (list_option_to_option_list xs); try easy.
    (* Some (a::l) = Some (a0::xs') *)
    inverts H.
    (* to get the IHxs conclusions *)
    assert (Some xs' = Some xs') by auto.
    apply IHxs in H; clear IHxs. destruct H.
    split.
    * (* length (Some a0::xs) = length (a0::xs') *)
      simpl. (* we know the tails have the same length *) now f_equal.
    * (* ∀ i, … *)
      destruct i; (* 0 *) try easy.
      (* S i *)
      simpl.
      (* at this point, exactly matches info from IH *)
      gen i. auto.
  - (* length … ∧ ∀ i … → list_option_to_option_list (a::xs) = Some (a0::xs') *)
    (* really only care about xs' *)
    specialize IHxs with xs'.
    (* make hyps more useable *)
    destruct H.
    inverts H.
    (* usualy analysis on a/xs *)
    destruct a; simpl.
    * (* Some a; need to handle match *)
      destruct (list_option_to_option_list xs).
      + (* Some l *)
        f_equal.
        (* need a = a0, l = xs' *)
        assert (a = a0). (* from the ∀ i *)
        { specialize H0 with 0. simpl in H0. now inverts H0. }
        subst. f_equal.
        (* now l from the IH *)
        enough (Some l = Some xs'). { now inverts H. }
        apply IHxs; clear IHxs.
        split; auto.
        (* careful with the index! hyp has nth_error (Some a0::xs), but we care
         * about nth_error xs *)
        intros. now specialize H0 with (1+i).
      + (* None, contradiction from the same reasoning *)
        enough (None = Some xs') by easy.
        apply IHxs; clear IHxs.
        split; auto.
        intros. now specialize H0 with (1+i).
    * (* None, also contradiction, but faster to find; the list shouldn't have
       * contained None *)
      now specialize H0 with 0.
Qed.

Inductive range: Type :=
  | Single: nat → range
  | Subrange: nat → nat → range
  | Fullrange: range
.

(* Compute firstn (5-(3-1)) (skipn (3-1) [1;2;3;4;5;6]). *)

Fixpoint index_by_range {A: Type} (m: matrix A) (ranges: list range): option (matrix A)
  :=
  match m with {| shape := m_shape; contents := m_contents |} =>
  if Nat.eqb (length ranges) (length m_shape)
  then
    match m_contents, ranges with
    | Scalar a, [] => Some {| shape := []; contents := Scalar a |}
    | Matrix [], ranges =>
        if forallb (λ r, match r with
                         | Fullrange => true
                         | _=> false
                         end) ranges
        then Some {| shape := m_shape; contents := Matrix [] |}
        else None
    | Matrix ms, rh::rt =>
        match rh with
        | Single n =>
            match nth_error ms (n-1) with
            | Some m => index_by_range {| shape := tl m_shape; contents := m |} rt
            | None => None
            end
            (* what if lo > hi? *)
            (* what if either out of bounds *)
        | Subrange lo hi =>
            let sublist := (firstn (hi-(lo-1)) (skipn (lo-1) ms))
            in let submatrices := map (λ m, index_by_range {| shape := tl m_shape; contents := m |} rt) sublist
            in match list_option_to_option_list submatrices with
              (* TODO tl m_shape bogus *)
               | Some ms' => Some {| shape := length ms'::tl m_shape; contents := Matrix (map contents ms')|}
               | None => None
               end
        | Fullrange =>
            let submatrices := map (λ m, index_by_range {| shape := tl m_shape; contents := m |} rt) ms
            in match list_option_to_option_list submatrices with
               | Some ms' => Some {| shape := length ms'::tl m_shape; contents := Matrix (map contents ms')|}
               | None => None
               end
        end
    | _, _ => None
    end
  else None
  end.
