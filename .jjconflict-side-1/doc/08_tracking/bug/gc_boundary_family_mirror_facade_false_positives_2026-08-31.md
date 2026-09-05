# gc-warning: family-mirror re-export shims reported as layering violations

- Filed: 2026-08-31
- Status: PARTIALLY FIXED (pure-Simple rule fixed; seed emitter unfixed — see "Seed half")
- Component: `35.semantics/gc_boundary_check.spl`, seed `interpreter_module/{module_loader,path_resolution}.rs`

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

## Seed half — NOT fixed, patches recorded

The 30 warnings observed above are emitted by the **Rust seed**
(`module_loader.rs:197`), whose family table is a hardcoded enum with no config
read, so there is no data-driven exemption. This session was barred from running
cargo, and landing unbuilt seed edits is what `check-seed-builds-push.shs`
exists to stop. Recorded rather than applied:

1. `path_resolution.rs` `preferred_stdlib_variant` — normalize separators before
   matching, so the own-family preference works on Windows:

        let base = base_dir.to_string_lossy().replace('\', "/");

   (markers stay as-is). This removes the round trip at its source and is the
   higher-value half — it also fixes silently resolving to the wrong family.

2. `module_loader.rs` `gc_boundary_warning_message` — port
   `is_family_mirror_facade`: after computing both families, return `None` when
   the two paths are equal with their family component stripped and the reason
   is `higher_layer_runtime_family`.

Until a seed is rebuilt, the observed count stays 30.

## Verification

| | before | after |
|---|---|---|
| `[gc-warning]` (seed emitter, frozen) | 30 | 30 |
| `[use-warning]` manifest symbol loss | 2 | 0 |
| spec result | 3 total, 3 passed, 0 failed | 3 total, 3 passed, 0 failed |
