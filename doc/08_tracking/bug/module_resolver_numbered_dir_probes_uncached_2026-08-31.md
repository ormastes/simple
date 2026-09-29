# Module resolver re-probes the numbered layer dirs on every import — 12-line fixture never finishes

- **Filed:** 2026-08-31
- **Status:** OPEN (fix in progress)
- **Platform:** observed on aarch64-apple-darwin; the code is platform-independent
- **Component:** `src/compiler_rust/compiler/src/module_resolver/resolution.rs`

## Symptom

`scripts/check/check-bootstrap-stage2-struct-receiver.shs` fails its positional
pure-Simple Stage-3 route with **status 124** — the `timeout` budget
(`STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS`, default 180s).

The input is a **12-line fixture**
(`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`)
built with `--threads 1`. Raised to a 2400s budget it still had not produced a
single byte of log output, at 93% CPU and **3.4 GB RSS**. This is not slowness
to be waited out.

Read the status carefully: **124 is a timeout, not a pass and not a crash.** It
was reached only after the separate `E-MIR-TYPE` defect was fixed (`6d3856e6b4b`);
before that the route failed earlier and faster, which is why this cost had never
been observed. It is a PRE-EXISTING cost newly reached, not a regression from
that fix.

## Cause

`sample <pid>` on the hung process, frame counts, most frequent first:

```
123 module_resolver::resolution::find_segment_within_numbered_dirs
 88 module_resolver::resolution::find_numbered_dir
 37 fs_probe::path_kind
 34 fs_probe::p_is_dir
 23 pipeline::native_project::imports::mangled_matches_use_path
 20 pipeline::native_project::imports::resolve_import_name_strict
```

`find_numbered_dir` (`resolution.rs:38`) and `find_segment_within_numbered_dirs`
(`resolution.rs:79`) each perform a fresh `std::fs::read_dir(parent)` plus a
`p_is_dir` per entry on EVERY call. Import resolution calls them for every import
of every file, so the same `(parent, segment)` pairs are recomputed an enormous
number of times against the compiler's own deep numbered-layer tree.

Confirmed by inspection: `resolution.rs` is 1052 lines and contains **zero**
`static` / `OnceLock` / `thread_local` / `Mutex` / `RefCell` — there is no cache
of any kind in the module resolver today.

## Same class as an already-fixed defect

`parsed_imported_module()` (`hir/lower/import_loader.rs`) had the identical shape:
`preregister_imported_type_names` and `load_imported_types` re-PARSED every
imported module on every `use`, giving **3,819** successful `.spl` `openat` over
423 distinct files for a lint of a TWO-LINE file, with `10.frontend/core/ast.spl`
parsed **866** times. Memoizing per process took it to 676 opens (5.65x) for
~110 MB RSS. See `.claude/rules/commands.md`.

The fix here should mirror that one, including its deliberate constraint: the
memo is **per process and never on disk**, because the repo depends on "edit
`src/lib`, no build needed" (the stdlib is read as source every run).

## Fix

Per-process, thread-safe memo keyed by `(parent, segment)` for both functions,
with the build-lifetime assumption stated in a comment. Semantics must be
preserved exactly, including the `!prefix.is_empty()` guard at `resolution.rs:47`
— without it every dotfile directory (`.git`, `.claude`) qualifies as a numbered
layer directory, because `all(is_ascii_digit)` is vacuously true for the empty
string.

## Not yet established

Whether the route COMPLETES once this is cached, or whether a further cost sits
behind it. A cached resolver is necessary here; it is not yet shown to be
sufficient. Do not record this gate as passing on the strength of this fix alone.
