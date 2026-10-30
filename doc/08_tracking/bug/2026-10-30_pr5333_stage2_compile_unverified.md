# PR #5333 self-hosted compiler changes were never compiled by a Stage 2 build

- Status: OPEN (blocked on host resources; not skipped silently)
- Found by: post-merge review of PR #5333, finding 5 (P1 context)
- Affected sources (Stage 2 inputs): `src/compiler/99.loader/module_resolver/{resolution,types}.spl`,
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`,
  `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl`,
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`

## Attempt 2026-10-30 (macOS arm64, 24 GiB RAM, ~44-63 GiB disk free)

Documented manual Stage 2 command (`.claude/rules/bootstrap.md` § Bootstrap Commands),
narrowed to `--source src/app/cli` per the worktree-trap note:

```
SIMPLE_BOOTSTRAP=1 <seed> native-build --source src/compiler --source src/lib \
  --source src/app/cli --entry src/app/cli/bootstrap_main.spl -o <scratch>/stage2_simple
```

1. Seed `src/compiler_rust/target/bootstrap/simple` (prebuilt authority, 2026-10-23,
   directory is read-only `dr-x`): fails before codegen with
   `error: semantic: dynamic SFFI dispatch has no compiler-owned ABI contract for function 'rt_io_file_open_read'`.
   The stale piece is the bootstrap-profile seed *compiler*: the ABI contract table lives in
   `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` (error raised from
   `interpreter_extern/dynamic_sffi.rs`). Rebuilding it in place
   (`cargo build --profile bootstrap -p simple-driver -p simple-native-all`) fails at once:
   `failed to open: target/bootstrap/.cargo-build-lock` because the frozen directory is
   read-only. Making it writable would replace the shared authority, so it was left alone.
2. Seed `src/compiler_rust/target/release/simple` (rebuilt from HEAD on 2026-10-30; not the
   canonical bootstrap seed, so this is a diagnostic proxy only):
   loads and checks the closure, then
   `error: build refused: 8325 MiB of RAM/commit headroom free, below the 24576 MiB reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)`.
   24 GiB is the host-independent compiler default
   (`doc/07_guide/tooling/bootstrap_native_staging.md` § "Configured headroom during Stage2
   sanity"); it cannot be satisfied on a 24 GiB host. The documented knob is a justified
   lane-specific `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`; it was not set here because this task
   was told not to change configuration.

Net: no Stage 2 compile of the #5333 `.spl` changes was possible on this host within the
45-minute budget.

## What is covered instead

Seed-interpreted specs now exercise the changed resolver and interpreter code:
`cached_directory_resolution_spec` 4/4 (after #5365 + #5366, which fixed three latent
resolver defects that no compiler had ever run), `tier_ambiguity_warning_spec` 6/6,
`enum_instance_method_dispatch_spec` 3/3 (#5349), `to_u64_unsigned_semantics_spec` 6/6
(#5370), `test/01_unit/compiler/frontend/flat_bridge_string_scan_spec.spl` 4/4. The MIR `to_u64` change is covered only by
`unsigned_conversion_result_spec` (lowering type), not by native execution.

## Unblock

1. Rebuild the bootstrap seed from HEAD into a writable target so the frozen
   `target/bootstrap/.cargo-build-lock` is never touched:
   `cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all --target-dir <writable>`.
2. On a host with enough headroom, or with an owner-approved
   `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`, run the Stage 2 command above with that seed and
   `SIMPLE_RUNTIME_PATH=<writable>/bootstrap` (bootstrap.md "Runtime Path Requirement").
3. Confirm the five files compile, then run `to_u64_unsigned_semantics_spec` natively.
