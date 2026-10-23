# Stage 2 (cranelift, core-c-bootstrap) HIR codec re-encode SIGSEGV on unlabeled `break`

- Status: open
- Severity: P1 — blocks the `--backend=cranelift` stage-2 admission sanity gate on Linux hosts without LLVM 23
- Found: 2026-10-19, release_phase3 @ 4ab52ecd1f0, host x86_64-unknown-linux-gnu

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --no-mcp --backend=cranelift`
builds stage 2 (1394 modules) and then fails the admission sanity probe
`stage2_module_path_naming`:

```
[hir-shard] owner=0/1@0 status=CRASH exit=-139 claimed=1 sealed=1 finished=false
error: HIR aggregate failure; final worker and artifact publication blocked
```

## Minimal reproducer

Any loop containing an unlabeled `break` crashes the stage-2 binary's HIR
codec round trip (`continue` does not):

```
fn f() -> i64:
    loop:
        break
    0

fn main():
    print(f())
```

Worker replay (SIGSEGV, rc=139):

```
SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_BOOTSTRAP=1 \
SIMPLE_RUNTIME_PATH=<stage3>/stage2-runtime-authority \
<stage2>/simple run src/app/cli/native_build_worker.spl \
  --backend cranelift --runtime-bundle core-c-bootstrap \
  --source src/compiler --entry-closure --mode one-binary \
  --entry <probe>.spl --output /tmp/probe
```

## Evidence

- Crash site: `compiler.hir.generated.hir_codec.hc_enc_hir_expr_kind` reading a
  two-slot enum payload `[3, 3]` (both slots the raw nil word;
  `rt_value_nil() == 3`) and dereferencing slot 1 as a pointer:
  `mov 0x18(%rax),%r8; mov (%r8),%r8` with `r8 = 3`.
- Stack: `hir_cache_store` -> `hir_cache_store_in_owned_scope` ->
  `hir_cache_selfcheck_blob` -> `hir_module_encode` (the decode -> re-encode
  round trip; the first encode of the lowered module succeeds).
- The decode side for `HirExprKind.Break(label: text, value: HirExpr?)` with a
  wire-nil label routes through `hc_restore_enum_nil` /
  `enum_wire_restore_nil` (`src/lib/nogc_sync_mut/sffi/enum_wire.spl`), which
  rebuilds the enum via `rt_enum_new` with the nil slot restored. The restored
  enum's payload tuple holds raw nil words in every nil/None slot.
- The SAME codec sources compiled by the Rust seed into a 366-module probe
  binary (same cranelift backend, same core-c-bootstrap runtime, same
  `--source` roots for src/compiler + src/lib, plus
  src/compositions/kernel_llvm_cranelift and the stage-2 env) round-trip the
  identical module cleanly (`37` / `\N` on the wire, ROUNDTRIP-OK), with the
  restored payload `[3, 3]` — the data shape is not the trigger.
- The crash therefore only manifests in the full 1394-module stage-2 build:
  same source, same backend, same runtime bundle, different whole-program
  context. This points at a scale-dependent miscompile or identity divergence
  in the seed-produced stage-2 image, not a codec logic error.
- The enum-wire restore boundary is documented as provisional and NOT
  runtime-qualified: `doc/bug/bugfix/a174_enum_scalar_codec_wire_boundary_2026_10_16.md`.

## Related

- `doc/08_tracking/bug/hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`
  (nil-word 3 confusion, encode side, fixed by rendering)
- `doc/08_tracking/bug/optional_nominal_enum_payload_provenance.md`
  (optional payload representation drift)
- PR #3892 `rt_heap_ref_registered` core-c guard (fixed the earlier
  all-refused codec symptom on this lane, not this crash)

## Next step candidates

1. In the stage-2 binary, compare the compiled optional-payload binding for
   `HirExprKind.Break` between the lowering-produced enum (works on first
   encode) and the `rt_enum_new` product (crashes on re-encode); the payload
   words are identical, so inspect enum identity/layout handling at scale.
2. Decoder-side fallback: when the runtime lane cannot restore nil slots
   safely, decode the label as `""` and let the selfcheck refuse the store
   (loud, no crash) instead of faulting.
