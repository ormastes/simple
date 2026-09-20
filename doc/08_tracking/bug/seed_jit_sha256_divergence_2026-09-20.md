# Seed JIT sha256 diverges from interpreter for multi-block inputs (interpreter matches ground truth)

- Status: OPEN (2026-09-20) — record-only; seed is bootstrap-only per project rules. Pure-Simple compiler fix + re-deploy needed.
- Found: 2026-09-20 (macOS unit-test sweep lane, kernel_plugin_schema fixture regeneration)
- Component: seed runtime/JIT (`src/compiler_rust`, Cranelift JIT lane of `bin/simple`); pure-Simple `std.common.crypto.sha256.sha256_text` itself is correct.

## Observation

`sha256_text` over the same 370-byte canonical KPF schema text:

- Interpreter lane (`bin/simple run`, module falls back to interpreter): `855e2c68...` — matches `shasum -a 256` / CPython `hashlib.sha256` exactly.
- JIT lane (spec executed via `bin/simple test`, `sha256_text` JIT-compiled): `b56b5457...` — wrong.

Short inputs hash identically in both lanes (e.g. `kpf.interface.v1\nexample.echo.Admin@2` → `774ef7ed...` everywhere, including the checked-in fixtures). A ~150-byte probe also agreed across lanes, so the divergence is length/pattern-dependent (370 bytes = 5 blocks + padding triggered it; the 1295-byte WIT text happened to hash correctly in the JIT lane).

Concrete impact (2026-09-20): `compile_kpf_schema` embeds `sha256_text(canonical)` into `KpfPackageIr.schema_digest`, so the digest — and every generated artifact that embeds it (`.rs`/`.hpp`/`.wit` fixtures, worker-wire module) — differs between lanes. The `test/01_unit/tool/kernel_plugin_schema` fixtures regenerated on 2026-09-20 pin the JIT-lane digest (`b56b5457...`) because `bin/simple test` is the standard runner; under a corrected toolchain they must be regenerated (the `.spl` pin and `generated_wit_fixture_test.shs` `shasum` pin agree today only because the spec-lane `sha256_text` of the 1295-byte WIT text coincides with its true hash).

## Fix direction

1. Root-cause the seed Cranelift codegen for `std.common.crypto.sha256` multi-block compression (likely a rotation/xor/schedule-index miscompile that only manifests past a block boundary).
2. Verify the same defect does not exist in the pure-Simple compiler's JIT path (`src/compiler`), then re-deploy the self-hosted binary.
3. After re-deploy, regenerate the KPF fixtures (`test/fixtures/kernel_plugin_schema/generated/*`, `test/01_unit/tool/kernel_plugin_schema/generated/example_echo_worker_wire.spl`) and update the two WIT hash pins — the fixture comments will visibly flip from `b56b5457...` to `855e2c68...`.

## Related

- `gpu_ffi_loader_probes_linux_sonames_on_macos_2026-09-19.md` (same sweep lane)
- `unit_test_sweep_macos_2026-09-17.md` (sweep context)
