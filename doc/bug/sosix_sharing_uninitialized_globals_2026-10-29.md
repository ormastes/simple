# SOSIX sharing globals omitted by bootstrap interpreter

Observed on release/1.0.0 at 45aac9d5f67 with the existing October 23 Rust bootstrap interpreter. All six cases in `test/03_system/app/os/feature/sosix_process_sharing_spec.spl` failed with `semantic: variable sosix_dataset_active not found`.

The module evaluator in `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs` evaluates `Node::Let` globals only when `stmt.value` is present. Thus initializer-less fixed arrays are not materialized on this interpreter route. The pure-Simple parser already synthesizes fixed-array defaults in `src/compiler/10.frontend/core/parser_decls_use.spl`; this report does not claim that route has the same defect.

SOSIX sharing now supplies explicit false/zero repeat-array initializers for all 22 state arrays, matching existing SOSIX process and I/O tables. Sizes, types, reset behavior, and handle semantics are unchanged. This is a bounded source compatibility repair, not a compiler workaround silently treated as a language restriction. The bootstrap evaluator omission remains an upstream runtime limitation.

Validation uses the authorized existing bootstrap with `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpreter` and `test <spec> --timeout=60 --format=text`. The six-case system specification passes after this repair. No Phase2 rebuild was performed.
