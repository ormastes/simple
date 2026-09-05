# Native object cache reuses dependents after a dependency's interface changes (2026-08-17)

Status: OPEN. Gate `scripts/check/check-native-object-cache-invalidation.shs` is
**advisory and honestly RED** on `main` today.

## Symptom (measured, not asserted)

Fixture: `leaf.spl` exporting `leaf_val()`, four `depN.spl` that each call it,
one entry `main.spl`. Rust engine (`SIMPLE_NATIVE_BUILD_RUST=1`,
`SIMPLE_NATIVE_INCREMENTAL=1`), receipt read back from stdout:

| scenario | reused / rebuilt | expected |
|---|---|---|
| cold | 0 / 6 | 0 / 6 |
| no change | 6 / 0 | 6 / 0 |
| `leaf` BODY edit | 5 / 1 | 5 / 1 |
| `leaf` INTERFACE edit (`leaf_val()` -> `leaf_val(bias: i64)`) | **5 / 1** | **1 / 5** |

The four dependents were compiled against a zero-argument `leaf_val` that no
longer exists, and were served from cache anyway. Object count in
`cache/objects` rose by exactly one across the interface edit, confirming the
four dependent cache KEYS did not change.

## Why the existing design was expected to catch it, and did not

`native_project/mod.rs:952` folds a `GlobalBuildFingerprint` into every
per-module key, whose `layout` component is
`cross_module_layout_fingerprint` (`mod.rs:1572`). That function folds
`result.fn_arities` and `result.fn_return_types` over the whole closure, so an
arity change was expected to change `global_fp_combined` and invalidate every
module. Measurement says it does not. Root cause not yet isolated; two
candidates, neither confirmed:

- `layout_fp` is computed only under `if !self.config.no_mangle`
  (`mod.rs:~930`), so a `no_mangle` build has `layout = 0`.
- `fn_arities` may not be populated for the functions in this fixture.

This is deliberately recorded as *unconfirmed* rather than guessed.

## Direction of the defect

Two opposite failures exist and must not be traded for each other:

- **Under-invalidation** (this bug): an entry whose inputs DID change is served.
  Cost is a silently wrong binary. Same fail-open class as `access.rs:288`'s
  `.unwrap_or(0)` field-index guess and `success()` returning true with zero
  tests run.
- **Over-invalidation**: an entry whose inputs did NOT change is discarded.
  Cost is time only. See the separate finding below.

## Separate, confirmed over-invalidation (bootstrap lane)

`scripts/bootstrap/bootstrap-from-scratch.sh:832-841`,
`bootstrap_wide_inputs_hash`, hashes the CONTENT of every
`src/compiler/**/*.spl` (`hash_path_list`, :692-696) into one stamp. On any
mismatch `prepare_native_cache` (:931-937) runs `rm -rf "${native_cache_dir}/"`.
So a one-line edit to ONE compiler source **destroys the entire per-lane object
cache**, forcing a full cold build. This is destructive, not merely a miss.

It is also largely redundant with the per-module key, which already folds
producer identity (`compiler_fingerprint()` = hash of `current_exe` bytes),
backend, opt level, CPU and SIMD tier — a changed compiler mints different keys,
so stale entries could never be *hit*. The inputs the wipe covers that the key
demonstrably does not are the `SIMPLE_*` `AOP|MDSOC|WEAV|LOAD|INTERPRET|
EXECUTION|LIB|NATIVE_BUILD` environment variables (:840). Folding those into the
key is the prerequisite for removing the wipe; removing the wipe first would be
fail-open.

## Pure-Simple engine: whole-closure object directory

`driver_native_sources_fingerprint`
(`src/compiler/80.driver/driver_aot_native_output.spl:262-283`) hashes every
loaded source's interface text into ONE manifest hash, which becomes a
DIRECTORY level: `rt_path_join(base_cache_scope_root, "sources-{fp}")` (:456).
Any interface edit anywhere mints a brand-new object directory, so reuse drops
to zero. Safe, but total over-invalidation. Note this engine is NOT on the
bootstrap path: stage 2 and stage 3 both run the Rust seed with
`SIMPLE_NATIVE_BUILD_RUST=1` (`bootstrap-from-scratch.sh:1892,:1953`,
`resume-stage3-from-admitted.sh:180`).

## Fix direction

Replace the single global `layout` blob with a per-module key of
`own source hash + interface digests of the modules it imports`.
`interface_digest_of` (`src/compiler/80.driver/cache/action_key.spl:199`)
already implements the canonical `simple/interface/v1` digest and has **zero
production callers** (only `test/01_unit/compiler/cache/action_key_spec.spl`).
`ActionDep.iface_digest` exists (`action_key.spl:33`) and is populated only by
`cache/integration/shadow_mode.spl:100`. `SmfManifestEntry`
(`80.driver/watcher/smf_manifest.spl:23-34`) carries `source_hash` and has no
interface-digest field.

Acceptance is the gate above going green in all four scenarios, plus a
cross-worktree warm-hit measurement, which has NOT been attempted.

## 2026-08-17 re-check (independent lane) — STILL OPEN, no code change made

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust bootstrap seed).

Mechanism re-confirmed unchanged in source:

```
$ grep -n "driver_native_sources_fingerprint\|sources-" \
    src/compiler/80.driver/driver_aot_native_output.spl
322:pub fn driver_native_sources_fingerprint(sources: [SourceFile]) -> text:
516:        val cache_scope_root = rt_path_join(base_cache_scope_root, "sources-{sources_fingerprint}")
$ grep -rln "interface_digest_of" src/compiler/80.driver/cache
src/compiler/80.driver/cache/block/block_key.spl
src/compiler/80.driver/cache/action_key.spl
src/compiler/80.driver/cache/schema/cache_protocol.sdn
```

The whole-closure fingerprint still names the object DIRECTORY. The
`interface_digest_of` name now appears in three files rather than one, but the
two extra hits are not the missing production caller this row asks for:
`schema/cache_protocol.sdn` is a schema declaration, and `block/block_key.spl:10`
is a COMMENT mentioning the name. `action_key.spl:199` is still the sole
`fn interface_digest_of` and its only definition. Nothing on the native-build driver
path calls it.

**The fix was deliberately NOT attempted in this lane.** Replacing the coarse
directory partition with per-module dependency edges converts a safe
over-invalidation into a potential UNDER-invalidation — the fail-open class this
row itself warns about — and it can only be validated by the four-scenario
measurement at the top (cold / no-change / body edit / interface edit). That
measurement cannot be taken right now: every native-build of even a ONE-module
fixture aborts before codegen with
`memory allocation of 2147483648 bytes failed` under the interpreted worker
(evidence and the driver-side misreport fix:
`doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`).
Landing an unverifiable invalidation change would risk silently wrong binaries,
so the row stays OPEN with its fix direction intact.

Prerequisite for anyone picking this up: get a native-build of a small fixture
to COMPLETE first, then re-run the four scenarios.
