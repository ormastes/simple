# Candidate-emitted HirTypeKind escapes codec and visitor (watcher_client, stage2 slim matrix)

Date: 2026-11-14
Lane: work/release-1.0.0-mcp-local (MSVC stage-2 bootstrap)
Tips reproduced: 228560191e0 (cycle 16), ff993c1134d (cycle 17)

## Symptom

`compiler_cli_build` (stage2-compiler-tests slim profile) dies in the HIR
phase at module ~2752-2760 of 3147 (deterministic across two cycles and two
tips, both jobs=1):

```
[hir-cache-store] refused reason=codec detail=unencodable HirTypeKind enum
  module=src/compiler/80.driver/watcher/watcher_client.spl; entry not stored
E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown> unhandled at walk_hir_type
```

Row: build/bootstrap/mcp-local/stage2-compiler-tests/x86_64-pc-windows-msvc/
verification/logs/compiler_cli_build.log (~4 MB; crash at the tail).

## Facts that narrow it

- `scripts/check/check-hir-codec-complete.shs` -> PASS ("99 declarations
  covered, generated codec fresh"). The generated codec/visitor cover all 31
  HirTypeKind variants (Int..Nil, tags 0..30); the encoder's `case _:
  w.reject("unencodable HirTypeKind enum")` (generated/hir_codec.spl:8947)
  and the visitor's E-HIR-VISIT-UNHANDLED fallthrough are unreachable for
  well-formed values. So the candidate produced a HirTypeKind value whose
  discriminant matches NO variant.
- The decoder's unknown-tag path rejects (`hc_bad_tag("HirTypeKind", tag)`)
  rather than synthesizing, and the row ran with `cached=0` (all 3147 modules
  recompiled), so the bad value is NOT a stale-cache decode artifact: the
  stage2 candidate's own frontend/lowering constructs it for this module.
- The SEED compiles the same source fine (the main stage2 native build
  completes all modules including watcher_client at the same tips), so this
  is a self-hosting parity gap: candidate-frontend output that the shared
  codec/visitor tables cannot represent.
- watcher_client.spl is mundane: 10 declarations, no exotic type surface
  (no Weak/Unique/Shared/Layer/Tensor/DynTrait/effects). The bad kind may be
  produced for an IMPORTED type flowing through HirModule.imported_layouts
  (hir_types.spl change 6bf24744e00, codec wire v17 bump c79be829a86 — the
  newest churn in this area) rather than for a source-level type in the file.

## Why filed instead of patched here

The v17 imported_layouts format and the HIR visitor/codec are under active
development by the HIR lanes (#9048 stage-3 MIR cluster, #9036/#9037, the
6bf24744e00/c79be829a86 pair). A blind codec arm addition risks masking a
frontend bug that produces the invalid discriminant in the first place.
The owning lane needs the producer-side diagnosis (which lowering path
constructs the out-of-range kind for this module).

## Repro

```sh
# any MSVC stage-2 bootstrap run at the listed tips reproduces; the failing
# row is compiler_cli_build in the slim phase-verification matrix
SIMPLE_BUILD_MEMORY_RESERVE_BYTES=1073741824 \
SIMPLE_HOST_CONFIG=$HOME/.config/simple/host.sdn \
SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=50331648 \
SIMPLE_NATIVE_FILE_TIMEOUT=1200 \
BOOTSTRAP_VERIFY_CAMPAIGN_TIMEOUT_SECONDS=21600 \
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
  --stop-after-stage2 --mode=dynload --jobs=1 \
  --output=build/bootstrap/mcp-local --no-mcp
```

Blocks: stage2 slim verification -> stage3/stage4 resume -> MCP lane on this
host class (all downstream work queues behind this one gate).

## Suggested next probes for the owner lane

1. Instrument `hc_enc_hir_type` / `walk_hir_type` to print the numeric
   discriminant + owning span of the offending HirType when the wildcard arm
   fires (one run answers "which tag, which construct").
2. Check the imported_layouts decode for watcher_client's imports: whether a
   v17 layout round-trips a kind the encoder later refuses (asymmetry).
3. Diff candidate vs seed frontend output for watcher_client (HIR dump both
   producers) to find the divergent construct.
