# Native object cache: duplicate-import witnesses were invalid; `-o` moved the object scope

Date: 2026-11-24
Branch: work/native-cache-witness-gaps-20261124 (base origin/release/1.0.0 @ 787a7205ec8)
Follow-up to PR #11162 ("Not fixed here").

Status: both fixes are **static reasoning plus spec only**. No spec and no build
was executed (no `bin/simple` on the host, a 40 GB build was running). Open
items are at the end.

## A. `native-module-cache-witness-v1-invalid`

### Evidence (cache `~/.simple/prov/p3r/cache`, read-only)

- 120 capsule receipts, 112 distinct modules, carry an invalid witness. All 120
  have the one reason `ambiguous-resolution-fact`.
- That reason is produced only by `native_module_cache_witness_v1`
  (`src/compiler/80.driver/cache/native_module_witness.spl`), for
  `selected_count != 1` or a repeated `import_id`. The retained-fact producer
  `native_resolution_facts_v1` already rejects `selected_count != 1` earlier
  under a different reason (`incomplete-resolution-trace`), so the live trigger
  is the repeated import id.
- Grouping the 541 distinct modules with a receipt by "does the source import
  the same module on more than one `use` line": invalid 112 of 112 yes
  (111 by a line regex, the last one, `virtual_source_registration_v1.spl`, by
  reading it: `use m (...)` next to `export use m.{...}`), valid 0 of 429 yes.
- Examples: `lib.nogc_sync_mut.io.group_process_owner`
  (`std.common.build_manager.group_process_protocol` twice),
  `lib.nogc_sync_mut.io.pipe` (`std.common.string_core` twice),
  `lib.scv.store` (`std.scv.core` twice), `compiler.frontend.core.lexer`,
  `compiler.frontend.core.parser`. Nothing else is common to them: not
  generated, not `__init__` facades, not empty modules.

### All reasons a witness can be invalid

`missing-module-or-mir-identity`, `missing-retained-native-input-facts`,
`unfrozen-native-input-surfaces`, `misaligned-retained-input-module`,
`missing-consumer-surface`, `missing-direct-dependency-routing`,
`unresolved-direct-dependency`, `missing-dependency-module-id`,
`ambiguous-dependency-source`, `missing-resolution-instrumentation`,
`misaligned-resolution-trace`, `incomplete-resolution-trace`,
`missing-layout-instrumentation`, `misaligned-layout-consumer`,
`missing-or-ambiguous-external-layout`, `fact-set-module-mismatch`,
`missing-module-id`, `missing-mir-identity`, `missing-config-fact`,
`missing-emitter-scheme`, `missing-dependency-fact`,
`ambiguous-dependency-fact`, `missing-resolution-fact`,
`ambiguous-resolution-fact`, `missing-layout-fact`, `ambiguous-layout-fact`.
Only `ambiguous-resolution-fact` occurs in the evidence cache.

### Decision: over-conservative, fixed

One trace per `use` line is recorded, so two lines naming one module give two
resolution facts with one import id. The rule "a repeated id is ambiguous" is
meant for one import resolving two ways. Now a repeat is compared with the
first fact's `resolution_witness_digest` (ordered probes, selection, directory
generation, resolver version): equal is folded once, different is still
`ambiguous-resolution-fact`. Nothing is dropped without that comparison and no
constant is introduced.

Why the witness still tracks its inputs:

- own source: `mir_identity`, unchanged;
- imported interfaces: the dependency fold. Both producers
  (`native_direct_dependency_facts_v1`,
  `native_direct_dependency_facts_from_index_v1`) already union the imported
  items of every `use` line per target, so no line's items are lost;
- resolution: each distinct import id still contributes its digest;
- codegen options: the config fingerprint, unchanged.

A module without repeated imports gets the same witness as before, so existing
valid receipts stay valid.

## B. Changing only `-o` gave a new object scope

`compile_targets.spl` exports `SIMPLE_NATIVE_NOOP_FINAL_OUTPUT=<output>`. Every
present `SIMPLE_*` variable is a row of the environment capture, and the module
projection (`native_build_module_environment_snapshot_fingerprint_v1`) did not
drop this one. The module environment digest goes into both the scope directory
(`s<hex>`, via the compiler id in `driver_native_build_cache_scope_for_compiler_id`)
and each witness's `options_identity`.

`native_build_cache_scope_key` itself folds no path. The variable has one
reader, `driver_native_noop_request_v1`, which uses the complete capture and so
still separates requests by output.

### Decision: accident, excluded from the module projection

- Not lane isolation: the lane is `SIMPLE_CACHE_SCOPE`
  (`per_lane_private_caches.md`), still folded twice. Two builds with the same
  `-o` already shared a scope, so the path never isolated concurrent writers.
- `options.output_file` is not read in `driver_aot_native_output.spl`; inside
  `compile_to_native` the `output` parameter reaches a trace line, the link and
  publication only.
- Other consumers of the module environment digest or the scope directory,
  read to see whether any is valid for one output only:
  - relink skip (`native_link_with_receipt_v2`): keyed by `output` itself, and
    its receipt is `<output>.link-receipt`;
  - whole-build no-op request: complete capture plus the output;
  - MIR-shard resume key (`native_mir_shard_run_key_v1`): also folds argv;
  - opt-in pre-lower cache producer identity: lowered MIR, no output use;
  - library-unit dyn-libs under `<scope>/units/<unit>/<key>/`: keyed by
    producer identity, source digest and dependency interfaces; soname is the
    file name and rpaths are `$ORIGIN` / `@loader_path`; they are copied beside
    the output on every build, reused or not;
  - `phase.marker`, `.cache_scope`, the witness shadow receipt: diagnostics
    rewritten by each build.
- The list this variable is in (`NATIVE_BUILD_NONSEMANTIC_ENVIRONMENT_FIELDS_V1`)
  already classes it as not changing artifact bytes.

## Open

1. Neither spec case has been run; no compiler containing the change has been
   built. Needed: a two-run probe on a fixture with a duplicated import
   (second run must hit) and one changing only `-o` (same `s<hex>`).
2. A: that the two traces of a repeated import are digest-identical at run
   time is inferred (same import text, same resolver, same frozen surfaces),
   not observed. If they differ the module stays invalid, which is safe.
3. B: only this fold was found by reading. The probe in #11162 was not
   repeated, so another output-derived value may exist.
   `SIMPLE_NATIVE_NOOP_CACHE_ROOT` (a cache location, same single reader) is
   left folded on purpose; it does not change with `-o`.
4. Still open from #11162: the witness config folds the frozen storage-registry
   identity, which may depend on which modules share a batch.
