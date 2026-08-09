# Feature Expert — Counterpart Conformance

## Role

Own process knowledge for the Counterpart Conformance Infrastructure: the single
differential/oracle pipeline under Modern SSpec that compares Simple against upstream
reference implementations (Chrome, HarfBuzz, SwiftShader/Venus, OpenSSL/Mbed TLS, zlib/zstd)
and against its own CPU/GPU execution modes.

There is exactly one such pipeline. If you are about to add a second differential framework,
stop — absorb it into this one instead.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- ADR (contract freeze): `doc/04_architecture/infra/adr/adr_counterpart_conformance_contract_freeze_2026-08-09.md`
- Design: `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`
- Plan (parallel agent waves): `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- Upstream dependency: `doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md`
- Architecture context: `doc/04_architecture/compiler/mdsoc_architecture_tobe.md` (MDSOC+ observation ports)

## Source Entry Points

| Path | Role |
|---|---|
| `src/lib/common/spec/evidence/counterpart/model.spl` | **Frozen** Wave-0 contracts. ADR amendment required to change |
| `src/lib/common/spec/evidence/counterpart/evidence_projection.spl` | CounterpartRun → CanonicalEvidence |
| `src/lib/common/spec/evidence/counterpart/manual_projection.spl` | CounterpartRun → ManualBlock[] (docgen renders, not this) |
| `src/lib/nogc_sync_mut/spec/evidence/counterpart/` | Registries, converter graph, relation engine, matrix, artifact store |
| `src/lib/nogc_sync_mut/sffi/counterpart_abi.spl` | Safe wrapper over the ABI shim; raw pointers never escape it |
| `src/runtime/counterpart_abi_runtime.c` | The only place dlopen/dlsym and raw pointers live |
| `tools/counterpart/sdk/c/simple_counterpart_abi.h` | `scf_api_v1`, ABI v1 |
| `tools/counterpart/adapters/` | Per-provider adapter libraries (`libsimple_counterpart_<id>.so`) |
| `config/counterpart/` | Provider descriptors, lockfile, profiles, schemas, plans |
| `test/01_unit/infra/counterpart/` | ABI, converter, relation, projection specs |

## Constraints a future agent will otherwise get wrong

- **The dynamically loaded object is a Simple-owned adapter, not the upstream library.**
  Chrome is process-driven, Vulkan dispatches through loader/layer/ICD, SPIRV-Cross has no
  stable C++ ABI. Never dlopen an upstream project directly.
- **`DynLib.call_n()` is not the transport.** Its call interface is integers only. The
  counterpart path uses `src/runtime/counterpart_abi_runtime.c`; do not widen DynLib with raw
  pointers.
- **Three receipt planes stay separate.** Logical artifact / execution receipt / provenance
  receipt. Collapsing them is how a GPU lane passes while running on CPU.
- **Unavailable is never PASS; crashed is not unavailable.** `ProviderStatus` keeps them
  distinct on purpose.
- **No exact relation may traverse a lossy converter.** The rule lives in exactly one place:
  `relation_requires_exactness` + `relation_max_permitted_loss_rank`. Do not re-derive it.
- **Normalization rules belong to named, versioned converters**, never to the comparator, so
  they appear in the generated manual.
- **`independence_group`, not provider count.** Two wrappers over one engine are one reference.
- **Consensus never outranks a normative vector** (`oracle_authority_rank`).
- **Compressed-byte equality is not the default** for compression formats — cross-decode and
  round-trip are; byte equality only under a declared canonical encoder profile or frozen vector.
- **Only genuinely corresponding web stages are compared.** Simple's flat SoA renderer does
  not map one-for-one onto Blink; tokenization/prepaint/compositor have no counterpart and
  must be marked non-corresponding rather than forced.
- **Production modules import no foreign provider types.** All upstream deps live in the
  test-only capsule and under `tools/counterpart/`.

## Verification commands

```bash
bin/simple lint <changed .spl files>          # must be 0 errors; SLOW, never kill early
bin/simple run test/01_unit/infra/counterpart/<spec>.spl
# NOT `bin/simple test` for typed-evidence specs — the daemon trips the 800-module import cap
```

Every lane must ship a sabotage that turns green to red. "The adapter ran" is not an
acceptance criterion — see the acceptance-gate table in the design doc.

## Current state (2026-08-09)

- Wave 0 complete: ADR + frozen contracts landed.
- Wave 1 in progress: F1 ABI/mock, F5/F6 converter graph + relation engine, F7/F8 artifact
  store + SSpec projection.
- Not started: F2 package/build resolver (lockfile records are declarations, not yet enforced),
  F3 isolated worker, F4 provider registry, F9 foundation red-team, and all of Waves 2–7.

## Update Rule

Update this file in the same change as any counterpart work: new links, new constraints
discovered, and the current-state section above.
