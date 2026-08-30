# Stage 2 worker stack overflow compiling advice_form.spl

**Status:** fixed and cleared by the next canonical cycle; successor blocker
tracked separately.
**Observed:** 2026-08-15.

The frozen transaction completed all four Rust authority Cargo builds, passed
the exact pre-publication frozen-manifest check, published the authority, and
entered Stage 2. The seed then aborted with exit 134. The exact first failure
in `stage2-native-build.log` was:

```text
thread 'compile-advice_form.spl' (...) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

The owner file is
`src/compiler/85.mdsoc/weaving/advice_form.spl`. The retained source manifest
contains 13,015 inputs and 12,409 Simple files: 1,749 compiler, 7,820 library,
and 2,616 application files. No Simple module completed, no Stage-3 or Stage-4
candidate was produced, and no sanity, essential-tools, deployment, or
rollback gate ran. Cycle 3 elapsed 12m34.09s with peak RSS 2,700,488 KiB.

Immutable cycle evidence is retained under
`build/native_probe/stage4-owner-20260815/cycle3-bootstrap.{log,status,time}`
and `summary.md`. The active `stage2-native-build.log` is overwritten by every
canonical retry and no longer contains this historical stderr.

The next canonical transaction passed the refreshed pre-publication manifest,
published the Rust authority, and entered Stage 2. This overflow did not recur.
That run exited 1 after 15m30.95s at 2,701,132 KiB peak RSS on the distinct
unqualified ChangeKind match recorded in
`stage2_incremental_change_kind_unqualified_match_2026-08-15.md`. It produced
no candidate, hash, smoke, deployment, or rollback evidence.

## Diagnosis (2026-08-15, scoped fix session — verification deferred to Codex)

**Classification: compiler recursion**, not source recursion and not an
undersized worker stack. The worker stack is already 16 MiB
(`NativeBuildConfig::default().stack_size`,
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:424`), and the
owner file is a 20-line payload-free enum — nothing in it recurses.

Mechanism, confirmed by static trace of the frozen seed's code path:

1. Every Stage-2 per-file worker (`compile_module_worker`,
   `pipeline/native_project/compiler.rs`) runs
   `Lowerer::register_global_enums()` **before** lowering its own file. That
   pass resolves every project-wide enum's variant payload types via
   `resolve_type` (`hir/lower/lowerer.rs:516` →
   `resolve_global_enum_variants`).
2. The whole-project metadata (`imports.struct_defs`,
   `pipeline/native_project/imports.rs:963 record_struct_fields`) records
   struct, class, **and enum-variant named-payload** layouts as raw parser
   `Type` specs — including self- and mutually-recursive layouts
   (`Node { children: Array<Node> }` shapes are common in the self-hosted
   compiler's AST/HIR model, 13,015 frozen inputs).
3. In the frozen `type_resolver.rs` (manifest SHA-256
   `b7e5bcc044ef…`), `resolve_type(Type::Simple(name))` for an unregistered
   global struct resolved **all field types first and registered the struct
   only afterwards**, with no in-progress marker. A recursive layout therefore
   re-entered `resolve_type` on the same still-unregistered name forever:
   unbounded recursion → 16 MiB stack exhausted → `exit 134`.
4. `advice_form.spl` is incidental: every worker runs the same global-enum
   pre-pass, so the first-scheduled worker names the crash. That is why 0 of
   12,409 Simple modules completed.

## Fix and live verification

Root-cause fix in the HIR lowerer's global-struct materialization, two parts:

- `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs` — before
  resolving a global struct's fields, register a stable named **placeholder**
  `HirType::Struct` (empty fields) so any self/mutual reference terminates at
  that TypeId (`update_named` keeps the TypeId stable,
  `hir/type_registry.rs:144`); and guard the re-materialization path with an
  in-progress set so a cycle returns the placeholder id instead of descending.
  The old resolve-fields-then-register fallback block is deleted
  (`debug_assert!(global_field_specs.is_none())` marks it unreachable).
- `src/compiler_rust/compiler/src/hir/lower/lowerer.rs` — new
  `materializing_global_structs: HashSet<String>` field, initialized in all
  three constructors.
- Follow-up in the same session (second landmine, found by static audit of
  the fixed path): the recursion guard alone leaves re-materialization
  unmemoized — every later resolve of an already-materialized global struct
  re-resolves all of its fields, so a diamond-shaped reference graph
  (`A -> {B, C} -> D`) goes exponential in TIME: Stage 2 would spin instead
  of overflow. Added `materialized_global_structs: HashSet<String>`
  (lowerer.rs, all three constructors) checked alongside the in-progress set
  in type_resolver.rs and inserted after a completed materialization. Sound
  because the whole-project specs are immutable per compile and field slots
  point at stable TypeIds (`update_named` refines placeholders in place), so
  a second materialization can never refine anything. Regression test:
  `test_global_struct_diamond_graph_materializes_in_linear_time`
  (32 diamond layers — 2^32 field resolutions without the memo; the test
  only completes when each layout materializes exactly once).

The regression file existed in the earlier manifest; its new test contents
required a manifest refresh. The tests fail by overflow/hang against the old
resolver and pass only with the guard/memo:

- `src/compiler_rust/compiler/src/hir/lower/tests/expression_tests.rs` —
  `test_global_enum_payload_materializes_self_recursive_struct` and
  `test_global_struct_materialization_preserves_placeholder_across_mutual_cycle`
  (exact incident shape: global enum payload naming a self-recursive /
  mutually-recursive global struct, resolved via `register_global_enums`).
- `src/compiler_rust/compiler/tests/import_reexport_hir.rs` — formatting only.

The first refresh produced historical manifest SHA-256
`172dc82b27fcd0622943f7cd3bb76765719810681ad6baeb7a692f14a9e706c3`
with all 27,066 entries verified. The later reviewed manifest was
`cdb15cf755ee14ba561d6dede841ba077a848a6fca9e5ef46863beb456dc5586`
with all 27,070 entries verified before authority publication. Its canonical
transaction compiled all 846 Stage-2 entry-closure modules and reached the
final link, so the recursive materialization failure is cleared in the heavy
environment as well as in focused tests.

## Completed focused and canonical verification

```bash
# 1. Focused regression tests (must pass; the first two overflow on the
#    frozen resolver, the third hangs without the materialized-set memo):
cargo test --release -p simple-compiler \
  test_global_enum_payload_materializes_self_recursive_struct \
  --manifest-path src/compiler_rust/Cargo.toml
cargo test --release -p simple-compiler test_global_struct_ \
  --manifest-path src/compiler_rust/Cargo.toml

```

Observed Stage-2 outcome: the `compile-advice_form.spl` worker and every other
entry-closure worker survived the global-enum pre-pass. The canonical run's
distinct first failure was the final-link `rt_file_sync` provider gap recorded
in `stage2_bootstrap_rt_file_sync_provider_missing_2026-08-15.md`.
