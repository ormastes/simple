# Stage 3 self-host HIR import cascade

Date: 2026-07-30  
Status: release blocker  
Release: `1.0.0-beta2`

## Reproduction

```sh
env SIMPLE_NO_STUB_FALLBACK=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --jobs=2 --no-mcp --full-cli \
  --output=build/bootstrap-beta2-local-attempt3
```

Stage 2 builds, links, and passes bootstrap sanity. Stage 3 fails closed while
the admitted Stage 2 runtime lowers the same compiler source.

Evidence:

- `build/bootstrap-beta2-local-attempt3/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- `build/release-beta2-evidence/linux-x86_64-attempt3/metrics.env`
- 14,597 HIR-lowering errors across 416 files
- first missing shared types: `NLLError`, `SdnValue`, `CompileOptionsHash`
- peak RSS: 4,875,144 KiB; elapsed: 1,471.98 seconds

## Expected

Stage 3 resolves the same public/re-exported compiler symbols accepted by the
seed-built Stage 2 compiler and produces an admitted pure-Simple runtime.

## Actual

Stage 3 reports a broad unresolved-type/name cascade beginning in
`src/compiler/driver/*.spl`, then spanning MIR optimization and backend
modules. This is not the earlier memory blow-up or native runtime link defect.

## Next action

Trace the first missing re-export (`NLLError`/`SdnValue`) through Stage 2
workspace/module indexing. Fix the shared import/re-export owner before
addressing downstream errors; the remaining 14,000+ diagnostics are treated as
one cascade. Re-run the full bootstrap only in a fresh session because this
session reached the mandatory three-cycle cap.
