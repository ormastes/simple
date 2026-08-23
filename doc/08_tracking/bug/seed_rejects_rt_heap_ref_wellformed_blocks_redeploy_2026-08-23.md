# Rust seed rejects `rt_heap_ref_wellformed`, blocking the bootstrap redeploy (2026-08-23)

Status: OPEN. Severity: blocks the redeploy that would deploy `7127df8d794`.

## Symptom (verbatim)

A Rust seed built from a CLEAN `origin/main` (`c1efb59cf09`) cannot compile a
three-line hello world:

```
$ cargo build --release --bin simple      # rc=0, 6m19s, from src/compiler_rust
$ <seed> native-build /tmp/hwb_aot.spl -o /tmp/hw_s3
error: semantic: unknown extern function: rt_heap_ref_wellformed
error: native-build worker exited with code 1
rc=1
```

This is NOT the known "simple-main seed is stale / its tree is dirty" story:
the binary was built minutes earlier from committed `origin/main` content, in a
private `CARGO_TARGET_DIR`, and run with cwd inside a clean worktree of the same
commit.

## Mechanism

`rt_heap_ref_wellformed` is a formation probe added as a driver fail-closed
guard (`57271d9ba49`):

- declared  `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:55`
  (`extern fn rt_heap_ref_wellformed(value: Any) -> bool`), called at `:142`
  and `:505`
- defined   `src/runtime/runtime_native.c:7441`, declared `src/runtime/runtime.h:587`
- mirrored  `src/runtime/simple_core/core_enum.spl:73`
- self-check `src/runtime/test/rt_heap_ref_wellformed_selfcheck.c`

Both runtimes define it; the **Rust seed's semantic extern registry does not
know the name**, so the seed rejects the compiler's own driver source. Because
stage1 is produced by the seed, this fails the whole bootstrap chain, not just
hello world.

This is the `unregistered_extern_silent_nil_2026-08-01` defect class in its
fail-closed direction: the extern is real and backed, and it is the seed's
registry that is behind the tree.

## Why it matters right now

`7127df8d794` (string-arm hijack of user struct/class methods) fixes the
AOT-capsule SEGV in Simple-side MIR lowering, but the deployed stage2 was built
by a stage1 carrying the UNFIXED rule, so the fix cannot take effect without a
redeploy. The redeploy starts at the seed, and the seed is blocked here. Until
this is fixed, no end-to-end "hello world compiles and runs on the self-hosted
binary" claim can be produced for that fix.

## Fix direction (not attempted here)

Register `rt_heap_ref_wellformed` in the seed's extern surface and give it an
interpreter binding with the same contract as `runtime_native.c:7441`
(1 only for a well-formed heap reference, 0 otherwise). A registry row alone is
not enough — the interpreter lane needs an implementation, otherwise the guard
at `driver_hir_pipeline_lowering.spl:142` becomes a silent-nil, which is exactly
the failure mode the guard exists to prevent. TODO: owner unassigned.

## Reproduce

```
git worktree add --detach <wt> origin/main
cd <wt>/src/compiler_rust && CARGO_TARGET_DIR=<dir> cargo build --release --bin simple
printf 'fn main():\n    print("hello world")\n' > /tmp/hwb.spl
cd <wt> && <dir>/release/simple native-build /tmp/hwb.spl -o /tmp/hwb   # rc=1
```
