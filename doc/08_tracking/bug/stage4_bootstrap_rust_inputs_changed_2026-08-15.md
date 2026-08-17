# Stage 4 bootstrap aborted because Rust inputs changed

**Status:** blocked before Simple source discovery. **Observed:** 2026-08-15.

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
