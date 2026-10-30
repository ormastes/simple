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
   The authority is stale against HEAD. Rebuilding it
   (`cargo build --profile bootstrap -p simple-driver -p simple-native-all`) fails at once:
   `failed to open: target/bootstrap/.cargo-build-lock` because the frozen directory is
   read-only. Making it writable would replace the shared authority, so it was left alone.
2. Seed `src/compiler_rust/target/release/simple` (rebuilt from HEAD on 2026-10-30):
   loads and checks the closure, then
   `error: build refused: 8325 MiB of RAM/commit headroom free, below the 24576 MiB reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)`.
   The reserve (24 GiB) equals this host's total RAM, so no native-build can start here
   without lowering the reserve, which is a configuration change and was not made.

Net: no Stage 2 compile of the #5333 `.spl` changes was possible on this host within the
45-minute budget.

## What is covered instead

Seed-interpreted specs now exercise the changed resolver and interpreter code:
`cached_directory_resolution_spec` 4/4 (after #5365 + #5366, which fixed three latent
resolver defects that no compiler had ever run), `tier_ambiguity_warning_spec` 6/6,
`enum_instance_method_dispatch_spec` 3/3 (#5349), `to_u64_unsigned_semantics_spec` 6/6
(#5370), `flat_bridge_string_scan_spec` 4/4. The MIR `to_u64` change is covered only by
`unsigned_conversion_result_spec` (lowering type), not by native execution.

## Unblock

On a host with >= 24 GiB free headroom (or with an owner-approved reserve), rebuild the
runtime authority from HEAD `src/runtime` into a writable bootstrap target, run the Stage 2
command above, and confirm the five files compile; then run `to_u64_unsigned_semantics_spec`
natively.
