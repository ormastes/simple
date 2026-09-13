# MIR scope cannot promote a lowering allocated before the scope

Status: source repair and native boundary regression pass; rebuilt compiler
sanity/admission remains pending. No full bootstrap was run for this repair.

## Failure and ownership contract

`driver_pipeline_lowering.spl` creates the shared `MirLowering` before each
module's `lower_module_transient_scoped` scope. The returned `MirModule` promotes,
but `rt_transient_heap_promote(self)` fails: the native receiver is a raw
aggregate whose allocation is absent from the current scope's registry.
Promoting a pre-existing raw aggregate also cannot discover children written
into it during this scope. Making a shallow owner snapshot would still leave
older nested raw carriers opaque.

The retained boundary is the lowering's field graph, not its old carrier.
`_MirLowering/transient_owner.spl` builds one managed `[Any]` inventory containing
all 101 `MirLowering` fields and all 37 fields of its nested `MirBuilder`,
`MirModule`, `SymbolTable`, and `MirTargetContext` carriers. It includes carriers
themselves, so replacement aggregates allocated in this scope survive too, and
explicit children, so older carriers do not hide new arrays or scalar strings.
Managed arrays/dictionaries expose their children through runtime traversal.
MIR reads SymbolTable entries without mutating their older raw payloads.

One promotion traverses the inventory; `rt_array_free` then releases only the
temporary inventory. This mirrors HIR's `module_surface_promote_roots`, avoids
one arena scan per field, and accepts nil/scalars as array elements rather than
invalid standalone promotion roots. The existing pause, error cleanup, returned
module promotion, and bootstrap-registry promotion sequence is unchanged.

## Evidence

- `sh scripts/check/check-mir-transient-scope-boundary.shs`: PASS, 15 invariants.
  Its 14 mandatory scanner fixtures reject unscoped entry/fallback paths,
  missing cleanup, missing ambient registry promotion, whole-owner promotion,
  missing text/nested roots, declaration drift, ignored promotion failure,
  missing inventory release, and roots added after promotion. The inventory is
  compared with declarations, not a frozen count. This is static evidence.
- `test/fixture/transient_scope/mir_owner_inventory_promotion.spl`: a separate
  native boundary regression with an owner allocated before two successive
  scopes. The old receiver promotion is rejected; the explicit inventory keeps
  the returned value, nested arrays, accumulated strings, nil, and scalars valid
  after scope end. Both prior and current module values are asserted.
- Frozen Rust bootstrap producer SHA-256:
  `e25bc95505cbb74a66fecebb342e297366919240aa41406c17870eaf77a493f5`.
  This producer is bootstrap diagnostic authority, not an admitted self-hosted
  compiler or performance-comparison participant.
- Native build: 1 module compiled, 0 failed, 2.2 seconds; arm64 Mach-O.
  Probe SHA-256:
  `ed6e5bf259b30858c013554f1ea2af4ac5ea6fc906ba568c844de5f3cd434593`.
  Execution exited 0 with
  `PASS: old-owner rejection and explicit nested/text/nil/scalar inventory survive two scopes`.
- Build/run logs: `build/native_probe/astra-mir-inventory/build.log` and
  `build/native_probe/astra-mir-inventory/run.log`.

## Reproduce the bounded native mechanism test

Run from this worktree, using separate output/cache paths:

```sh
mkdir -p build/native_probe/astra-mir-inventory/tmp
env TMPDIR="$PWD/build/native_probe/astra-mir-inventory/tmp" SIMPLE_NO_STUB_FALLBACK=1 \
  sh scripts/bootstrap/run-process-group-timeout.shs 120 5 \
  build/macos-stage4-deploy/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple native-build \
  --source test/fixture/transient_scope --entry-closure \
  --entry test/fixture/transient_scope/mir_owner_inventory_promotion.spl \
  --target aarch64-apple-darwin --backend llvm --runtime-bundle core-c-bootstrap \
  --runtime-path build/macos-stage4-deploy/stage3/aarch64-apple-darwin/stage2-runtime-authority \
  --threads 2 --timeout 60 --mode dynload \
  --cache-dir build/native_probe/astra-mir-inventory/cache \
  -o build/native_probe/astra-mir-inventory/probe
build/native_probe/astra-mir-inventory/probe
```

## Remaining integration gate

The immutable `simple.rejected` contains the old compiler implementation.
Source edits cannot change its behavior; rerunning it does not test this repair.
The native fixture validates the boundary mechanism, not all production fields
or the entire compiler. A new Stage 2 built from these sources must pass the
canonical sanity and admission receipts before downstream use. The existing
cache-preserving, Stage-2-only canonical command is:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap \
  --backend=llvm --mode=dynload --stop-after-stage2 --jobs=2 \
  --output=build/macos-stage4-deploy
```

This command is documented, not executed in this repair: the parent lane's
full-build retry cap remains in force. Do not promote the rejected candidate or
weaken the transient-scope/ambient-registry boundary to make it pass.
