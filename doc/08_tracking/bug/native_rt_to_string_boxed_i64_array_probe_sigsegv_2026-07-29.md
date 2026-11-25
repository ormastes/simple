# Native `rt_to_string` boxed-integer array probe SIGSEGV
## Closed 2026-11-25 — RESOLVED; the 2026-09-16 "Open — needs owner triage" header was stale (the body's Status section already recorded the fix as resolved and verified)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## 2026-11-25 verification (work/p2w4-ae-20261125, origin/release/1.0.0 HEAD ef6a94f8a03)

The fix described below is present in the tree at release/1.0.0 HEAD, verified
by code inspection: `rt_to_string` (`src/runtime/runtime_native.c:5135`)
probes aggregates via `rt_core_as_registered_array` (`runtime_native.c:5146`),
the exact-registry-membership helper defined at `runtime_native.c:3151`, and
the regression selfcheck `src/runtime/test/rt_to_string_registry_selfcheck.c`
exists. Runtime execution was not re-run: the pinned seed
(`bin/simple.exe`, Rust v1.0.0-rc.1) cannot run any spec at this HEAD
(repo-wide `unknown decorator '@representation_boundary'` from cfd89933699),
and rebuilding the C runtime/native docgen is out of lane scope. The
2026-09-16 normalization pass missed the body's own Status/Fix/Evidence
sections when it stamped the header "Open"; the Status section's
"Resolved and verified" record stands. Header corrected; closing.

## Status

Resolved and verified with a rebuilt phase-2 pure-Simple docgen. The dependent
browser CSP and JS reclamation prerequisite commits still require their own
manual-quality review before they can ship.

## Symptom

The pure-Simple SPipe doc generator exited 139 after parsing and validating an
ordinary modern SSpec, before writing its Markdown manual.

## Root cause

`get_current_date()` interpolated the year 2026. Native `rt_to_string` probed
arrays before its scalar-integer arm with `rt_core_as_array`. The boxed integer
`2026 << 3` is the aligned value `0x3f50`, so the trusted raw-array helper
treated it as a pointer and dereferenced `kind`.

A bounded GDB run stopped in `rt_core_as_array` with `rdi=0x3f50`. Reduced
docgen fixtures proved the crash was generic and unrelated to CSP, HTML, or the
browser import graph.

## Fix

The aggregate probe now uses `rt_core_as_registered_array`, which checks exact
registry membership before dereferencing while preserving both tagged and raw
registered array handles. The trusted internal `rt_core_as_array` ABI remains
unchanged.

## Regression evidence

`src/runtime/test/rt_to_string_registry_selfcheck.c` registers a real array,
then proves boxed 2026 formats as `2026` and the registered array formats as
`[7]`.

```text
RT_TO_STRING_REGISTRY_SELFCHECK: PASS
```

Reverting the registered-array probe reproduces the boxed-integer SIGSEGV.

## Phase-2 docgen evidence

The phase-2 build completed with `69 compiled, 0 failed`. Its exact binary is:

```text
/tmp/simple-docgen-rt-to-string-fix/spipe_docgen_fixed
sha256=f9a5abc6bd1333de4c298c85dea03eb579e155e100eccdca5200c696051c489f
```

That binary regenerated both affected manuals without crashing:

```text
doc/06_spec/01_unit/os/hosted/hosted_browser_renderer_policy_spec.md
DONE Generated 1 docs (1 complete, 0 stubs)

doc/06_spec/03_system/feature/web_platform/js/js_event_dispatch_vm_reclamation_spec.md
DONE Generated 1 docs (1 complete, 0 stubs)
```

Build and generation logs are retained under
`/tmp/simple-docgen-rt-to-string-fix/`. No full bootstrap or Rust-seed fallback
was used.

