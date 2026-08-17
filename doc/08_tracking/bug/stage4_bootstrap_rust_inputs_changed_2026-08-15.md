# Stage 4 bootstrap aborted because Rust inputs changed

**Status:** blocked before Simple source discovery. **Observed:** 2026-08-15.
**Status:** RESOLVED AS INTENDED FAIL-CLOSED AUTHORITY REJECTION.
**Observed:** 2026-08-15. **Audited:** 2026-08-17.

The canonical `bootstrap-from-scratch.sh --full-bootstrap --deploy` attempt
aborted while preparing the Rust seed with:

```text
error: Rust inputs changed during full bootstrap; refusing to publish a stale seed
```

No Stage 2, Stage 3, or Stage 4 Simple source inventory was reached. Therefore
the truthful counts are zero Simple files compiled, zero Simple file failures,
and one bootstrap provenance failure. The 17 dirty Rust paths are input changes,
not compilation failures.

At freeze time the ordered dirty-path/content fingerprint was
`91339a9a754e88d7a93be848cd5b803781879947bee8a3399f4a90acf819d45d`.
The affected paths were:

- `src/compiler_rust/common/src/runtime_symbols.rs`
- `src/compiler_rust/compiler/src/hir/lower/type_registration.rs`
- `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`
- `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
- `src/compiler_rust/compiler/src/interpreter_call/mod.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `src/compiler_rust/compiler/src/interpreter_method/special/concurrency.rs`
- `src/compiler_rust/compiler/src/mir/lower/tests/branch_coverage/calls.rs`
- `src/compiler_rust/compiler/src/pipeline/mod.rs`
- `src/compiler_rust/compiler/src/value.rs`
- `src/compiler_rust/compiler/tests/import_reexport_hir.rs`
- `src/compiler_rust/native_all/src/lib.rs`
- `src/compiler_rust/parser/src/types_def/mod.rs`
- `src/compiler_rust/runtime/src/concurrency/mod.rs`
- `src/compiler_rust/runtime/src/executor_tests.rs`
- `src/compiler_rust/runtime/src/lib.rs`
- `src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/swapchain.rs`

## Last successful self-hosted Stage 4

The last located successful build is the 2026-07-30 full-CLI build from source
commit `9ea0b39962d76929ac58598d837f9292f3ebf6af`: 1,490 files,
26,709,488 bytes, 251 seconds, and SHA-256
`39a507b917c8d05583c386a7f2a27d195ddb0ecc0a702de487e07aff51378483`.
It was not deployed because its interpreted `run` path dropped string
interpolation. It is historical diagnostic evidence, not current admission.

## Restart condition

Before retrying, freeze every bootstrap-consumed source and script. Recompute
the fingerprint immediately before launch and before seed publication; any
change must abort. Other agents may edit documentation or unrelated projects,
but must not edit compiler, runtime, bootstrap, or shared build inputs until the
transaction completes.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: bootstrap-stage blocker; needs a full `--full-bootstrap` run, which this lane
may not perform (never build the main compiler). Nothing about the Rust-input
change detection can be re-measured without actually entering the stage.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## 2026-08-17 closure audit

The abort was the required safety behavior, not a missing Stage-4 compiler
fix. The current Rust-authority transaction fingerprints inputs before Cargo,
after Cargo, and again while holding publication authority immediately before
commit. The fingerprint covers all non-target files under `src/compiler_rust`,
discovered Cargo path dependencies inside the checkout, hosted runtime inputs,
`Cargo.lock`, `VERSION`, selected platform/backend/features, LLVM authority,
the resolved `rustc` and `cargo` binaries plus version output, target C tools,
and all four exact Cargo build recipes. Symlinked inputs and dependencies
escaping the checkout are rejected. A mismatch at either post-build boundary
aborts before authority publication, which is exactly what protected the
2026-08-15 run from publishing a stale seed.

The adjacent failure path is also fail-closed: fingerprint helper errors retain
the phase, status, private scratch directory, and stderr manifest; a later
successful fingerprint removes stale error evidence. Focused bounded evidence:

`sh test/01_unit/scripts/bootstrap_fingerprint_tmp_contract_test.shs`

passed once with `bootstrap fingerprint tmp contract: PASS`, including the
simulated ENOSPC rejection and recovery case. No admitted bounded continuation
artifact was present, so no full bootstrap was started. A future retry only
needs a stable ownership window for the already-enforced input set; weakening
or bypassing the mismatch gate would reintroduce the defect.
