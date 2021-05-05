# Proofs about [zelda-mosaic](https://github.com/benknoble/zelda-mosaic)

[Presentation](https://docs.google.com/presentation/d/1EaC5zwNfbskH0kabnuDZeTFLvrv6lRGhcaaQgWXeWxU/edit?usp=sharing)

Directories:
- `proposal`: Project proposal
- `progress-report`: Progress report
- `paper`: Final paper

Files:
- `Makefile`: compatible with GNU make to build the project using `coq_makefile`
- `_CoqProject`: describes the projects files and options
- `LibTactics.v`: the [Software Foundations](https://softwarefoundations.cis.upenn.edu) tactics library
- `LibMatrix.v`: implements matrix operations
- `microMatlab.v`: the main entry point, providing syntax and semantics for the
  language

## Todo

- correct two bugs in `nth` (0 is incorrect) and `index_by_range` (returned
  shape in some cases is incorrect)
- spec/prove `nth` and `index_by_range`
- finish implementing matrix operations
- complete `eval_exp` for expressions
- add states
- define semantics
- prove `zelda-mosaic` terminates

## Done

- syntax of expressions (`exp`) and statements (`statement`) (almost) completely
  defined
- matrix type defined (`matrix`, `matrix_content`), complete with specialized
  induction principle (`matrix_content_ind_strong`) and multiple views on
  well-formedness (`well_formed'`/`well_formed`, `well_formedI'`/`well_formedI`)
- tactics and hints for matrices and theorems (`wf_easy`, `matrix` hint db)
- proofs that the different definitions of well-formedness agree
  (`well_formed_agree`/`well_formed'_agree`)
- a shape-computing (`compute_shape`) function that preserves well-formedness
  (`compute_shape_wf_normalizes`)
- a linearization operation that supports `nth`, which behaves like MATLAB's
  matrix indexer of a single index for a multi-dimensional matrix
- proof that `linearize` preserves well-formedness (`linearize'_product`,
  `linearize_wf`)
- an auxiliary data function (`list_option_to_option_list`) to invert `list
  (option A)` to `option (list A)`
- proofs that it has the correct behavior
  (`list_option_to_option_list_none_iff_contains_none`,
  `list_option_to_option_list_some_iff_all_some`)
- attempts to define `nth` and `index_by_range` functions to support (limited)
  indexing functionality
