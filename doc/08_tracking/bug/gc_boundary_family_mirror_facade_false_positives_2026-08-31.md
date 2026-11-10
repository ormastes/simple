# gc-warning: family-mirror re-export shims reported as layering violations

- Filed: 2026-08-31
- Status: FIX IMPLEMENTED / VERIFICATION PENDING (2026-11-08)
- Component: `35.semantics/gc_boundary_check.spl`, seed `interpreter_module/{module_loader,path_resolution}.rs`

Seed-half resolution: `path_resolution.rs` now normalizes native and mixed
Windows separators before own-family matching. `module_loader.rs` exempts
structural family-mirror facades only for `higher_layer_runtime_family`;
non-mirror async-to-sync, GC, and no-alloc violations remain enforced. Focused
Rust regressions cover all four cases. `cargo check -p simple-compiler --lib`
passes. The focused test target remains unexecuted because unrelated existing
test-code errors (`E0433`, `E0283`, `E0624`) stop `cargo test`; no focused-test
pass is claimed.

## Symptom (measured)

`bin/simple.exe test test/01_unit/lib/common/crypto/bytes_to_hex_guard_spec.spl`
emits **30 `[gc-warning]` lines over 23 distinct modules**, all
`higher_layer_runtime_family`, e.g.

    [gc-warning] Higher-layer module 'std.nogc_sync_mut.test_runner.doctest_runner'
      (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut)
      (higher_layer_runtime_family)

Test result itself is unaffected: `3 total, 3 passed, 0 failed`.

## Root cause

28 of the 30 warnings name a module whose *importer* is a one-line re-export
shim. **All 49 files under `src/lib/nogc_async_mut/test_runner/` are pure
`export use std.nogc_sync_mut.test_runner.<same-name>.*` shims** — no
declarations, no executable code.

They are load-bearing. `src/lib/nogc_sync_mut/test_runner/` contains **34 files
that import siblings by the preferred bare spelling** `use std.test_runner.X`
(`structure.md`: "`use std.X` preferred"). Bare `std.X` resolves through a fixed
family search order that tries `nogc_async_mut` **first**:

- pure-Simple resolver — `10.frontend/core/interpreter/module_loader_resolve.spl:215-217`,
  deliberate: *"Default app mode is nogc_async_mut. Search order: nogc_async_mut
  (default) > ... > nogc_sync_mut (sync fallback)"*.
- seed resolver — `path_resolution.rs:876-882`, same `nogc_async_mut`-first list.

So a `nogc_sync_mut` module importing its own sibling is routed
**sync -> alias shim (async) -> back to sync**, and the shim, whose family is an
artifact of which directory the alias target had to live in, trips the rank rule
(`nogc_async_mut` rank 2 < `nogc_sync_mut` rank 3).

The rule already sees through one alias class (`resolve_gc_alias`) but had no
notion of a family-mirror facade.

The remaining **2 of 30** (`std.io`, `std.nogc_sync_mut.spec`) are genuine
async->sync crossings and are **left firing on purpose** — they belong to the
193-violation backlog noted in `.spipe/import-warning-debt/state.md`.

### Seed-only aggravating factor (Windows)

`path_resolution.rs:447-462` `preferred_stdlib_variant` would make an importer
prefer its own family and avoid the round trip entirely. It matches with
**hardcoded forward slashes**:

    let marker = format!("/src/lib/{variant}");
    base.contains(&format!("{marker}/")) || base.ends_with(&marker)

Observed importer paths on this host are mixed-separator, e.g.
`C:\Users\ormas\dev\simple\src/lib\nogc_sync_mut\test_runner\test_runner_files.spl`
— the segment after `lib` is a **backslash**, so the marker never matches and the
own-family preference silently dies on Windows.

## Real correctness bug found alongside

The shim `src/lib/nogc_async_mut/test_runner/test_manifest.spl` used a *curated*
re-export list (the only one of the 49 that does) which had drifted from the
real module's 17-symbol export surface, dropping 5 names. Symbols genuinely
vanished:

    [use-warning] 'manifest_covers' is named in `use std.test_runner.test_manifest.{...}`
      but module '...nogc_async_mut\test_runner\test_manifest.spl' does not provide it
      (imported from ...nogc_sync_mut\test_runner\test_runner_files.spl)

Same for `manifest_merge_roots`. FIXED: list completed to all 17 exports.

## Fixed here (pure-Simple, verifiable)

`35.semantics/gc_boundary_check.spl` — added `family_relative_subpath` and
`is_family_mirror_facade`, consulted **only** at the `imported.rank >
source.rank` branch. Two paths are a mirror facade when they are identical after
each has its own leading family segment stripped, and the families differ.
Scoped to the rank rule on purpose: a mirror that also crosses the GC or
no-alloc boundary still hard-fails, because those rules constrain what the
forwarded-to code may *do*, not where it *sits*. Pinned by two new sdoctests on
`check_gc_boundary_imports` (mirror exempt; non-mirror async->sync still fires).

## Seed half — implemented 2026-11-08

1. `path_resolution.rs` `preferred_stdlib_variant` normalizes separators only
   on Windows, so mixed-separator own-family matching works without changing
   POSIX backslash filename-byte semantics. The POSIX regression is retained.
2. `module_loader.rs` `gc_boundary_warning_message` ports the structural
   `is_family_mirror_facade` comparison with the same platform-aware separator
   handling. The exemption applies only to `higher_layer_runtime_family`;
   genuine async-to-sync, GC, and no-alloc violations remain active.

Focused Rust regressions cover mirror exemption, non-mirror warnings,
resource-boundary preservation, mixed Windows separators, and POSIX filename
bytes. `cargo check -p simple-compiler --lib` passes. The focused test target
is blocked by unrelated existing test-code errors (`E0433`, `E0283`, `E0624`),
so these new tests are not claimed as executed.

## Historical pure-Simple verification

| | before | after |
|---|---|---|
| `[gc-warning]` (seed emitter, frozen) | 30 | 30 |
| `[use-warning]` manifest symbol loss | 2 | 0 |
| spec result | 3 total, 3 passed, 0 failed | 3 total, 3 passed, 0 failed |

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: FIXED — VERIFIED on refreshed seed (verification no longer
pending).** This run is the seed-side verification the 2026-11-08 entry left
pending.

Repro on refreshed seed (build-commit 0791c2b7f4a7, 2026-11-11 build):
`SIMPLE_LIB=src bin/simple.exe test
test/01_unit/lib/common/crypto/bytes_to_hex_guard_spec.spl
--mode=interpreter --no-cache` → exit 0, **3 total, 3 passed, 0 failed**.

Warning analysis (full log captured):

- **0 of 49 `[gc-warning]` lines name a `test_runner` module.** All 28
  family-mirror facade false positives from the 2026-08-31 measurement are
  eliminated — the exemption works on the refreshed seed.
- The 49 lines name only 12 distinct modules — `nogc_sync_mut.io.{dir_ops,
  external_text_io,file_ops,process_ops}`, `io_runtime`,
  `sffi.{diag,env,fs,system_env_core}`, `shell.shebang_script`,
  `simd_crypto`, `spec` — each verified to be a REAL implementation
  (41–3289 source lines, no one-line `export use` re-export shim). These are
  genuine async→sync higher-layer crossings, the class this doc deliberately
  leaves firing ("left firing on purpose"); they belong to the broader
  violation backlog, not to this bug. `nogc_sync_mut.spec` is one of the two
  genuine warnings named in the 2026-08-31 body; the genuine set has simply
  grown with the lib since then.

Fix lineage cited:

- Pure-Simple half: `ebcef7d2e368` (2026-08-31, `fix(semantics): exempt
  family-mirror re-export shims from the layer-rank rule`) — `is_family_
  mirror_facade` in `35.semantics/gc_boundary_check.spl` + sdoctests +
  `test_manifest.spl` export-surface repair.
- Seed half: `0ee4e247c0dd` (2026-11-08, `fix(runtime): align heap ABIs and
  mirror facades`) — `path_resolution.rs` separator normalization +
  `module_loader.rs` structural mirror exemption; confirmed an ancestor of
  the refreshed seed's build-commit `0791c2b7f4a7`.

Also per the 2026-11-08 entry: focused Rust regressions were written but not
executed (unrelated E0433/E0283/E0624 test-code errors); that gap stands —
this verification is the spec-level repro only. No change made in this lane.
