(* This is the syntax and semantics for μ-MATLAB *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Program.
Require Import Floats.
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import microMatlab.LibMatrix.

Module Syntax.

  (* TODO
   * - matrices
   * - define values
   * - write exp_eval
   * - define state (FMapAVL on Strings to values)
   * - define semantics *)

  Definition var_name: Type := string.
  Definition matrix_t: Type → Type := matrix.

  Inductive exp: Type :=
    (* simple literals *)
    | IntLiteral: Z → exp
    | FloatLiteral: PrimFloat.float → exp

    (* basic arithmetic *)
    | AddExp (left: exp) (right: exp)
    | MultExp (left: exp) (right: exp)
    | DivExp (left: exp) (right: exp)
    | EqualsExp (left: exp) (right: exp)
    | NotEqualsExp (left: exp) (right: exp)
    | LTEqualsExp (left: exp) (right: exp)
    | Floor (num: exp)

    (* variables *)
    | VarRefExp (var: var_name)

    (* ranges *)
    | RangeExp (start: exp) (stop: exp)

    (* matrices *)
    | MatrixLiteral (values: matrix_t exp)
    | IndexExp (var: var_name) (indexer: exp)
    | SqueezeExpr (matrix: exp)
    | SizeExpr (matrix: exp)
    | LengthExpr (matrix: exp)
    | ProdExpr (matrix: exp)
    | SumExpr (matrix: exp)
    | MinExpr (matrix: exp)
    | MaxExpr (matrix: exp)
    | PointWiseExpExp (base: exp) (pow: exp)
    | ZerosExp (vector: exp)
    | OnesExp (vector: exp)
    | InfExp (vector: exp)
    | FindExp (cond: exp)
    .

  (* numel = prod . size *)
  Definition numel: exp → exp := ProdExpr ∘ SizeExpr.
  (* ndims = length . size *)
  Definition ndims: exp → exp := LengthExpr ∘ SizeExpr.

  (* propositional predicates that may be useful for the syntax *)
  Definition numberp: exp → Prop := λ e,
    (∃ z, e = IntLiteral z)
    ∨
    (∃ f, e = FloatLiteral f).

  Definition indexp: exp → Prop.
  Admitted.

  Definition falsep: exp → Prop.
  (* IntLiteral, equal to 0
   * or Empty Matrix
   * or Matrix containing something false *)
  Admitted.
  Definition truep: exp → Prop := not ∘ falsep.

  Definition vectorp: exp → Prop := λ e,
    ∃ vs, (e = MatrixLiteral vs
    ∧
    length (shape vs) = 1).
  Definition matrixp: exp → Prop := λ e,
    (∃ vs, e = MatrixLiteral vs).

  Inductive statement: Type :=
    | NoOp
    | Error
    | ExprS (e: exp)
    | AssignS (var: var_name) (value: exp)
    | IndexedAssignS (var: var_name) (index: exp) (value: exp)
    | SeqS (ss: list statement)
    | WhileS (cond: exp) (body: statement)
    | IfThenElseS (cond: exp) (thenS: statement) (elseS: statement)
    .

  Definition forloop (var: var_name) (range: exp) (body: statement): statement.
    (* := *)
    (* SeqS [ *)
    (*   (1* todo empty range? *1) *)
    (*   AssignS var (first of range); *)
    (*   WhileS (values left in range) (SeqS [body; AssignS var (next of range)]) *)
    (* ]. *)
  Admitted.

End Syntax.

Module Semantics.
End Semantics.
