# Stage-2 self-hosted compiler SEGVs in native_entry_closure_request_open_v1

**Status:** open. **Found:** 2026-10-05. **Blocks:** Stage 3 on Linux and Windows.

## Symptom

The admitted-shape Stage 2 compiler (`stage2/<triple>/simple.rejected`) fails the
`p2_add-build` sanity probe (rc=124 under the 180 s bound). Run directly, it
crashes before HIR lowering:

```
#0 compiler.driver.driver_build.native_entry_closure_owner.native_entry_closure_request_open_v1
#1 CompilerDriver.load_sources_impl
#2 CompilerDriver.compile_with_reverse_reference_owner_v1
#3 CompilerDriver.compile
#4 compiler_driver_run_compile
```

Same frame with and without `--entry-closure`, with sharding on (HIR shard
worker CRASH, claimed=0) and off (`SIMPLE_HIR_SHARDING=0 SIMPLE_PARSE_SHARDING=0`).

## Pre-existing on origin/main

Reproduced byte-for-byte frame on an unmodified `origin/main` `73150c2673f`
Stage 2 built with the identical lane:
`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=half`
(Linux/WSL, `SIMPLE_NATIVE_FILE_TIMEOUT=1800`, `LLVM_CONFIG` pointed away from a
dangling-canonicalization llvm-config). Windows MSVC Stage 2 fails the same probe
and segfaults in `load_sources` for both baseline and branch.

## Repro

```sh
SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_HIR_SHARDING=0 SIMPLE_PARSE_SHARDING=0 \
SIMPLE_BINARY=$C SIMPLE_BIN=$C SIMPLE_RUNTIME_PATH=<stage2-runtime-authority> \
$C native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry src/compiler/bootstrap_admission/p2_add.spl --mode one-binary --output p2_add
```

## Likely shape

The crashing frame first reads `request.binding.policy_digest`; a struct-typed
`NativeEntryClosureRequestV1` reaching native code malformed (nested struct
field read through a by-value struct parameter).
