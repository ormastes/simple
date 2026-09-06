# Stage 4 bootstrap aborted because Rust inputs changed

**Status:** historical provenance abort cleared; refreshed frozen baseline
verified. **Observed:** 2026-08-15.

The currently authorized manifest contains 27,070 entries, has SHA-256
`cdb15cf755ee14ba561d6dede841ba077a848a6fca9e5ef46863beb456dc5586`,
and passed a complete 27,070/27,070 verification. The abort below remains the
original incident record, not the current bootstrap frontier.

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

## Frozen retry outcome

## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: bootstrap-stage blocker; needs a full `--full-bootstrap` run, which this lane
may not perform (never build the main compiler). Nothing about the Rust-input
change detection can be re-measured without actually entering the stage.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## Status re-check 2026-08-17 — STILL BLOCKED, precondition re-measured

binary identity: `readlink -f bin/simple` = `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`; `stat -c '%s %y'` = `59537240 2026-08-17 12:58:51.339525019 +0000`

The blocking precondition (concurrently-edited Rust inputs in this shared
working tree) is still true today — the guard would fire again on any
`--full-bootstrap`:

```
$ git status --porcelain src/compiler_rust src/runtime
 M src/compiler_rust/compiler/src/codegen/instr/core.rs
 M src/compiler_rust/compiler/src/hir/lower/expr/operators.rs
 M src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs
 M src/compiler_rust/compiler/src/interpreter/expr/calls.rs
 M src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs
 M src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs
 M src/compiler_rust/compiler/src/interpreter_extern/system.rs
 M src/compiler_rust/parser/src/lexer/strings.rs
 M src/compiler_rust/runtime/src/value/core.rs
 M src/compiler_rust/runtime/src/value/sffi/env_process.rs
 M src/runtime/runtime_process.c
?? src/compiler_rust/target_wt/
?? src/runtime/runtime_terminal_mode_impl.h
?? src/runtime/runtime_terminal_signal_scope_impl.h
```

Note the dirty set is DIFFERENT from the one frozen on 2026-08-15 (11 tracked
files vs 17, only a partial overlap), which is itself the evidence that the tree
is still being edited concurrently. No full bootstrap was attempted — running one
was explicitly out of scope for this session, and doing so under these conditions
would reproduce `Rust inputs changed during full bootstrap` rather than teach
anything new. The guard is correct; the environment still cannot satisfy it.
Requires a quiesced tree or a private worktree with a frozen `src/compiler_rust`.
Nothing changed.
