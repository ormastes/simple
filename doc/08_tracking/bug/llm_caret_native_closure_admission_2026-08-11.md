# LLM Caret Native Closure Admission Failure — 2026-08-11

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom

`bin/caret --help` and `bin/caret --tui` correctly fail closed with exit 127:
no cached native Caret artifact exists. A cache-preserving native closure probe
then exposed a linker failure rather than an executable Caret surface.

## Root Causes

1. `src/app/llm_caret/messaging/cli.spl` imported `process_run_inherit` through
   `app.io.mod`, which does not export it. Native lowering emitted the bare
   `_process_run_inherit` symbol instead of the runtime-owned
   `_rt_process_run_inherit`. The import now names
   `app.io.process_ops.{process_run_inherit}` directly.
2. The core-C runtime had no terminal ABI provider for raw mode, terminal size,
   TTY detection, or byte input. `src/runtime/runtime_terminal.c` now owns that
   ABI and both core-C archive builders include it.
3. A full Caret closure still needs an admitted simple-core archive for the
   tagged filesystem ABI and a duplicate-safe native thread callback provider.
   The legacy broad `runtime.c`/`runtime_thread.c` objects must not be added
   blindly because they overlap existing core-C owners.

## Why Existing System SSpec Did Not Catch It

The cached CLI and PTY SSpecs assert the qualified-artifact success path, but
their prerequisites never had a mandatory native-entry build gate. The plan
described missing artifact execution as "blocked" and recorded zero scenarios,
so the unbuilt delivery artifact was not promoted to a release failure.

## Prevention

`scripts/check/check-llm-caret-native-closure.shs --check` is the required
pre-SSpec release gate. It rejects bootstrap/seed runtimes, absent or ambiguous
simple-core archives, stub fallback, failed entry-closure builds, missing
artifacts, and unresolved Caret ABI symbols. It retains build arguments,
stdout/stderr, exit status, `nm` output, and provenance under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_native_closure/`.

The corresponding modern SSpec and manual document the positive admission
path. A missing artifact is no longer a skipped or zero-execution result: the
direct gate exits 1 with `failure_class=release_gate`.

## Required Completion Evidence

1. A self-hosted, non-seed runtime and a matching simple-core archive make the
   native closure gate pass.
2. The resulting artifact is installed with provenance for `bin/caret`.
3. Cached CLI, cached plain hidden-CLI, and PTY TUI system checks pass with
   retained output and ANSI evidence.

## 2026-08-27: pre-existing RED confirmed during SSDOC-TRC-003 fix

test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl scores
49 -> 89 after repairing the mangled `# @req` block and binding
NFR-LLM-CARET-TUI-006 (comment-only edit, no behavior change). The spec is RED
before and after: `Results: 2 total, 0 passed, 2 failed`, both scenarios fail
with `expected 1 to equal 0` — check-llm-caret-native-closure.shs exits 1 on
this host. Proven pre-existing via in-place `git show HEAD:` restore
(identical Results). Left RED. Mutation check (to_equal(0)->to_equal(7)) also
reports 0/2 as expected but is weak evidence since the spec already fails.

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: needs a self-hosted non-seed runtime and a matching simple-core archive to run the native closure gate; this host only has the Rust seed. No change made.

## 2026-11-04 dependencies

Native closure admission cannot go green until the MIR/HIR closure failures are
resolved: native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19 and
caret_closure_enum_payload_binding_collection_gaps_2026_11_03. Both need a
stage3 producer to enumerate remaining diagnostics (TEST_BLOCKED on seed).

## 2026-11-05 note (mirp2-B)
Misbucketed under "closures": this is native *link-closure admission* (runtime
archive providers: tagged filesystem ABI, duplicate-safe thread callback), not
lambda lowering. MIR lambda lowering itself is verified working natively
(see native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19.md). Left OPEN;
next step: admit a simple-core archive owning the tagged fs ABI and re-run the
cache-preserving Caret closure probe.

## Addendum 2026-11-11 — lane p3-caret1: BLOCKED (out of scope; grant intact)

Traversed on work/p3-caret1-20261111 (origin/release/1.0.0 tip 79d5af6723f6).

- Nothing about this row is fixable from a bug lane: admission requires a
  self-hosted, non-seed runtime plus an admitted simple-core archive owning the
  tagged filesystem ABI and a duplicate-safe thread callback provider, then a
  cache-preserving entry-closure native build of src/app/llm_caret/main.spl.
- Entry-closure native builds are forbidden in-lane (campaign rule). This host
  only has the tracked Rust seed; the sanctioned path is the full bootstrap.
- No commit at tip references this bug id with an absorber; the dependency
  caret_closure_enum_payload_binding_collection_gaps_2026_11_03 fix
  (00e1c8a97203) IS an ancestor of tip and verified separately by this lane.

Verbatim grant (re-recorded intact): produce the self-hosted non-seed runtime
and matching simple-core archive via the sanctioned bootstrap
(`SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.shs
--full-bootstrap --deploy`), then run
`sh scripts/check/check-llm-caret-native-closure.shs --check`; when it exits 0
with retained nm/provenance evidence, install the artifact for bin/caret,
re-run the cached CLI + PTY TUI system checks, and only then close this row.

Status stays OPEN.
