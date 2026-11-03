# Text methods on text unwrapped from an optional: Cranelift JIT result typing

Canonical bug ID: `interp_option_unwrapped_text_starts_with_nil_2026_10_19`

Status: OPEN (P1) — historical source fix merged; durable verification pending.

## Corrected classification

The historical bug row called this an interpreter failure. The source fix and regression describe a Cranelift JIT failure in Rust-seed HIR lowering. The tree-walking interpreter was reported correct. The original symptom was that `starts_with` and `ends_with` on `text?` values unwrapped with `!` or `??` produced unboxed results (for example, true appearing as `nil`, false as `0`), breaking storage-root containment and downstream MCP caret tools.

## Fix in current release source

Fix commit [`51bbcd83e28523cc3c32684a920260e9ef4819fd`](https://github.com/ormastes/simple/commit/51bbcd83e28523cc3c32684a920260e9ef4819fd) is an ancestor of the current `release/1.0.0` target. It narrows the `text?` force-unwrap result to `STRING` in `lower_try` at `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2967`, and narrows `text? ?? text` to `STRING` in `lower_coalesce` at line 2212. The tagged heap text representation is preserved, allowing the JIT text-method result path to box its bool/integer results correctly.

The fix commit adds two executable artifacts:

- `test/01_unit/compiler/unwrapped_text_method_dispatch_jit_probe.spl` — standalone per-engine probe. It covers `!` and `??` text methods, positive and negative results, use in a branch and bool argument, plus `contains`, equality, and related text-method controls.
- `test/01_unit/compiler/unwrapped_text_method_dispatch_spec.spl` — interpreter assertions and named-engine execution of the probe for `interpret` and `jit`.

## Historical validation and limit

The fix commit message reports that the pre-fix probe had 16 incorrect checks and the spec had 3/4 passing; after a cargo-built producer whose SHA-256 prefix was `76f06e7c7176df3a`, the probe passed and the spec passed 4/4. Those results are reported history: raw output logs and a producer receipt are not committed with the change. This record does not claim a new FC56 or current-host run, Phase 3 qualification, native execution, or release-wide admission. The database remains open while durable verification is pending.
