# Native object cache evicts the WHOLE closure on any interface edit

Date: 2026-08-17
Status: OPEN (defect precisely localized; fix not yet landed)
Lane: build-manager (implementing
`doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md`)

## Summary

The pure-Simple native build reuses cached objects correctly for **body-only**
edits, but an edit to any module's **interface surface** evicts every other
module's object in the build, including modules with no dependency relationship
to the edited one.

## Measured (this is the BEFORE baseline)

Fixture: 3 modules. `main.spl` imports `leaf_a` and `leaf_b`; `leaf_a` and
`leaf_b` are unrelated to each other.
`/mnt/data/tmp/.../scratchpad/reusefix/{main,leaf_a,leaf_b}.spl`

Invocation (a STABLE private cache dir, receipts read back per the plan doc):

```
bin/simple run src/app/cli/native_build_main.spl \
  --entry <fixture>/main.spl -o <out> --cache-dir <fixture>/c2
```

Receipt line counted: `[NATIVE] cache hit: <module>`
(`driver_aot_native_output.spl:536`).

| run | change | cache hits | `sources-*` scope dirs |
|---|---|---|---|
| b_cold | none (cold cache) | **0 / 3** | 1 |
| b_unchanged | none | **3 / 3** | 1 |
| b_after_edit | `leaf_a` body `1` -> `11` | **2 / 3** (leaf_b, main) | 1 |
| b_iface_edit | `leaf_a` gains `pub fn leaf_a_extra()` | **0 / 3** | 2 |

Soundness spot-check: after `b_after_edit` the rebuilt binary printed `13`, so
the 2/3 reuse was a correct reuse, not a stale-object false hit.

## The stale premise this corrects

The lane brief (and `.claude/rules/commands.md`) states the driver "hashes the
ENTIRE loaded source closure into `cache_scope_root`, so editing any ONE file
drops reuse to 0 for every module (measured: 3/3 reused unchanged, 0/3 after a
one-line edit)".

**That no longer reproduces for a body edit.** `driver_native_sources_fingerprint`
(`driver_aot_native_output.spl:369-390`) was already changed to hash only the
ABI-visible portion of each source via `driver_native_source_interface_text`
(:299), explicitly so "a body-only edit to one module does not change this
fingerprint". Measured above as 2/3, not 0/3. That half of the complaint is
already fixed; it landed on or before `d0fa6bf20931` / `ae55a7467197`
(2026-08-11).

**The other half is real and reproduces exactly**: the fingerprint is still a
WHOLE-CLOSURE hash of every source's interface text, so one interface change
anywhere renames the `sources-<fp>` scope directory and every module misses.
`leaf_b` has no relationship to `leaf_a` and was still rebuilt from scratch.

## Mechanism

- `cache_scope_root = base_cache_scope_root + "sources-{sources_fingerprint}"`
  (`driver_aot_native_output.spl:456` region) partitions objects by a hash of
  the whole closure's interface text.
- `driver_native_build_filter_scoped_outputs` (:315) requires every cached
  output path to start with that root, so a cross-fingerprint reuse is
  impossible by construction — a new scope dir is an unconditional full rebuild.
- `BuildCache` per-entry validation is already per-module and content-keyed
  (`has_cached_object`, `incremental.spl:524`), so the coarse directory
  partition is the only thing forcing the over-eviction.

## Why the coarse partition exists, and what replaces it

It is a sound stand-in for dependency tracking: without per-edge validation,
evicting everything is the only safe response to an interface change. The
targeted fix is the plan's typed dependency edges:

1. `DependencyEntry.dependencies: [text]` already exists and is already
   serialized — but the single writer passes `[]`
   (`driver_aot_native_output.spl:258`), so it is always empty.
2. `DependencyEntry.needs_recompile` (`incremental.spl:280-306`) already
   implements per-dep staleness and is **never called**. Note it currently
   fails OPEN on a dep missing from `dep_cache` (`if dep_cache.has(dep)`); a
   dep-edge check must fail CLOSED.
3. Per-module interface text is already available from
   `driver_native_source_interface_text` — the same function the closure hash
   uses. Applying it per module rather than over the closure needs no new
   digest code.

With those wired, an interface edit to `leaf_a` invalidates `leaf_a` and its
actual dependents (`main`) only, leaving `leaf_b` reused: 1/3 instead of 0/3 on
this fixture, and O(dependents) instead of O(all modules) at scale.

## Other unwired prior art found (all real, all with zero callers)

- `interface_digest_of` (`80.driver/cache/action_key.spl:199`) — zero call sites.
- `compile_interface_digest` / `compile_interface_parts`
  (`35.semantics/interface/compile_interface.spl`) — a complete
  CompileInterfaceDigest over `ApiSurface`, bodies excluded by construction.
- `compute_module_identity` (`35.semantics/interface/module_identity.spl:84`) —
  produces all four identities the plan names; comment reads "Entry point for
  later agents".
- `change_classifier.spl` (`src/app/build/targets/`) — already distinguishes
  `implementation_changed` from `compile_interface_changed`.

Blocker for using `compile_interface_digest` directly from the driver:
`ApiSurface` lives in `src/compiler/90.tools/api_surface.spl` (layer 90, ABOVE
80.driver) and has **no ParserModule extractor in Simple** — it is populated via
SFFI. `35.semantics` importing `compiler.tools.api_surface` is itself a layer
inversion. So the driver-side slice should digest `ParserModule` /
`driver_native_source_interface_text` directly rather than route through
`ApiSurface`.

## Also found

`SIMPLE_NATIVE_BUILD_CACHE_DIR` is **not** honoured by the native-build worker
subprocess: a run with that env set still wrote to `build/native_cache`. Use the
`--cache-dir` flag, which does work. An env-only invocation silently measures a
shared, contended cache.

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
