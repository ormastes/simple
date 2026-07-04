# Feature: field-wrapper-cache-and-lint

## Raw Request
formal verify current have hole on field wrapper. 1. update simple to prevent it. 2. check formal verification it prevent that. 3. cause warning use of get/set dummy. whuch just return just set, however one of them is not dummy get set not show warning. it is overriding get/set then do not warn. check all get set is start. 4. on lint, fast similar name function with parent class warn possible missspell. sesrch web find fast algorithm for it deeply. with "@name_checked" suppress it. $sp_dev

## Task Type
bug

## Refined Goal
Prevent stale field-wrapper-dependent code from surviving cache/JIT reuse, prove that prevention in the formal verification cache model, and add lint warnings for dummy accessor methods and likely misspelled parent method names with an explicit `@name_checked` suppression.

## Acceptance Criteria
- AC-1: A change to a wrapped field's public accessor/layout semantics invalidates every cached interpreter SMF, loader module, compiler artifact, and JIT generation that compiled a dependent field access against the old semantics.
- AC-2: Cyclic dependencies such as `A -> B.field -> A` are invalidated as one dependency group rather than leaving any member compiled against stale field-wrapper semantics.
- AC-3: The formal verification usage for compiler cache correctness includes a field-wrapper semantic dependency case and fails closed when the dependency fingerprint changes.
- AC-4: Focused formal verification/cache tests pass for the field-wrapper invalidation model.
- AC-5: Lint emits a warning for trivial `get_*`, `set_*`, and `is_*` accessor methods that only expose or assign a backing field and add no behavior.
- AC-6: Lint does not warn when any related accessor pair/group contains real behavior, and does not warn for accessor methods that intentionally override a parent method.
- AC-7: Lint emits a fast possible-misspelling warning when a child class method name is edit-distance-similar to an inherited method name but is not an exact override.
- AC-8: `@name_checked` suppresses the possible-misspelling warning for an intentionally distinct child method name.

## Scope Exclusions
- No release/tag work unless explicitly requested after verification passes.
- No GUI, Draw IR, or web-renderer changes in this lane.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: bug).
- agent-a: Added Pure Simple semantic/public-ABI field-wrapper invalidation hooks for verification, incremental cache, loader, and JIT paths; targeted checks currently type-check but runtime specs still fail in the dirty workspace.
- agent-a-final: Pure Simple formal/cache lane completed. Formal fingerprints now include public ABI/accessor/field-wrapper semantic inputs; verification cache invalidates transitive/cyclic dependents; incremental and SMF loader semantic fingerprints fail closed on stale dependency metadata.
- agent-b-final: Pure Simple lint lane completed. `ACC001` warns on trivial `get_*`/`set_*`/`is_*` accessor groups unless the group has real behavior or overrides a parent; `NAME001` warns on close inherited-method misspellings and `@name_checked` suppresses it.
- dev-final: Integrated runtime loader invalidation so semantic changes drop module metadata and JIT semantic keys together. Fixed Pure Simple semantic hash helpers to use stable escaped/content fingerprints instead of broken text iteration/overflow-prone arithmetic.
- verify: `SIMPLE_LIB=src bin/simple test/00_formal_verification/compiler/cache_correctness_spec.spl` -> 22 examples, 0 failures.
- verify: `SIMPLE_LIB=src bin/simple test/01_unit/compiler/loader/module_loader_semantic_cache_spec.spl --mode=interpreter --clean` -> 3 passed, 0 failed, including loader dependency cycles and JIT semantic-key invalidation.
- verify: `SIMPLE_LIB=src bin/simple test/01_unit/app/lint_spec.spl` -> accessor/name lint examples included, 17 examples, 0 failures.
- verify: `SIMPLE_LIB=src bin/simple test/02_integration/app/verify_test_quality_gate_spec.spl` -> 12 examples, 0 failures.
- verify: `bin/simple check` on changed Pure Simple lint, verification, incremental, and loader files -> all checks passed.
- verify-rust-seed: `CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=/tmp/simple-rust-seed-target cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml` -> passed.
- verify-rust-seed: Rust lint seed tests `accessor` and `similar_parent_method_name` -> 4 tests passed, 0 failed.
- verify-rust-seed: Rust incremental seed test `test_semantic_field_wrapper_change_invalidates_cached_dependent` -> 1 passed, 0 failed.
- verify-layout: `find doc/06_spec -name '*_spec.spl' | wc -l` -> 0.
- doc: Updated `doc/01_research/domain/field_wrapper_cache_and_lint.md` so the initial failed formal-cache findings are followed by the resolved passing evidence.
