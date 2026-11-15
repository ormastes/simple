# Core interpreter cannot load `compiler.core.*` from a guest program

- **Date:** 2026-11-14
- **Severity:** P3
- **Status:** fixed
- **Component:** `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`
- **Regression spec:** `test/01_unit/compiler_core/interpreter/module_loading/nested_numbered_layer_import_spec.spl`
- **Found by:** residual 1 of `core_array_cow_spec_timeout_2026-11-14.md`

## Symptom

A program run through `core_jit_interpret` that contains
`use compiler.core.ast_expr.{...}` (or any other `compiler.core.<module>`) stops with
`failed to load module: compiler.core.ast_expr`. The last red example of
`test/01_unit/compiler/interpreter/core_array_cow_spec.spl` ("isolates real
ExprStoreState constructor getter and installed nested snapshots") failed this way.

## Root cause

`core` is not a numbered layer. There is no `src/compiler/core` and no
`src/compiler/NN.core`; the package is `src/compiler/10.frontend/core`, nested inside the
`10.frontend` layer. The pure-Simple resolver's numbered-directory walk
(`resolve_with_numbered_dirs`) tried only two things for each intermediate segment: a
direct child and an `NN.segment` directory. `core` matched neither, the walk returned
`""`, and `resolve_module_path` fell through to the unresolved relative path
`compiler/core/ast_expr.spl`, which does not exist.

The Rust seed resolves the same import because its
`resolve_with_numbered_dirs_recursive`
(`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`) has a third
strategy, `find_segment_in_numbered_dirs`, that looks for the segment inside each
numbered layer, and it backtracks when a candidate directory does not hold the module.
That is why every host-side `use compiler.core.*` works while the same line in a guest
did not: the two resolvers disagreed. The module path in the fixture is current and
correct; the fixture was not changed.

## Fix

`resolve_with_numbered_dirs` and `_resolve_transparent` now share one walk,
`_resolve_dir_chain_leaf`, which tries for each intermediate segment, in order: the
direct child, the `NN.segment` layer, then every `<NN.layer>/segment` directory in sorted
order. A candidate whose subtree does not contain the module is abandoned for the next
one. The walk returns only files that exist. The digit-prefix test that was written out
inline in `find_numbered_dir_interp` moved to `_numbered_dir_prefix_len` so both lookups
use one definition.

The nested-layer strategy runs only after every cheaper strategy has missed, and the
result is cached per (module, importing file).

## Evidence

Seed built at `0b184f840a0`, sha256
`220e1bea5833bd0ea705dc96cbfba0044d4d146cda2c41b33440bd2e4aa4557e`, aarch64.

| spec | before | after |
|---|---|---|
| `core_array_cow_spec.spl` | 24 of 25 | 25 of 25 |
| `nested_numbered_layer_import_spec.spl` | 3 of 6 (the three nested-layer cases fail) | 6 of 6 |

Direct resolver output before the fix: `compiler.core.lexer` gave
`compiler/core/lexer.spl`, while `compiler.frontend.core.lexer` gave
`src/compiler/10.frontend/core/lexer.spl`.

The other 55 specs swept serially (27 in `test/01_unit/compiler_core/interpreter/`, 12
`test/01_unit/compiler/interpreter/` neighbours, 14 in
`test/01_unit/compiler/module_resolver/`, plus the two resolver specs) keep identical
verdict lines before and after: 48 OK and 7 red on both sides. The 7 are red on the base
and are not caused by this change: `lib_entry_app_prefix_import`, `type_domain_resolver`,
`array_method_set`, `array_parameter_copy`, `bare_case_ident_variant_pattern`,
`coverage_unary_not_probe`, `dotq_cross_engine_parity`. Summed wall time for the whole
sweep was 451 s before and 473 s after; the difference is the ExprStoreState example now
running to completion.

The fixture dates from `630ceb192f0` (2026-11-07) and the pure-Simple resolver has never
had the nested-layer strategy, so the example has not passed under the core interpreter
before; this is a missing capability, not a regression.

## Residuals

- Precedence: the numbered-layer walk runs before the `_`-transparent fallback, so a
  nested-layer hit now wins over a transparent-folder hit. The reviewer found no module
  name where the two disagree today.
- A package name that exists in several layers (`perf`, `backend`, `cache`, `lint`,
  `verify`, `generated`) resolves to the first layer in sorted order that holds the
  module, as in the seed. No spec pins that ordering yet.
- The leaf is tried as `name.spl` only; the seed also accepts `__init__.spl` and `.shs`.
  Unchanged from before.
- The seed has two more strategies (dotted directories such as `app/ui.tauri`, and
  joining several pending segments into one dotted directory name). They are not ported
  here; no failing guest import needed them.
