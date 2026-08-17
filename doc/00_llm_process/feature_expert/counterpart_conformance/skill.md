# Feature Expert — Counterpart Conformance

## Role

Own process knowledge for the **Simple Counterparts Compare Test** — the program name for
the Counterpart Conformance Infrastructure: the single differential/oracle pipeline under
Modern SSpec that runs Simple and an independent open-source counterpart over the SAME
input at a frozen boundary (`<domain>.<mdsoc-layer>.<stage>@<schema-version>`, e.g.
`vulkan.shader.spirv_binary@1`) and compares under a declared relation, against upstream
reference implementations (Chrome, HarfBuzz, SwiftShader/Venus, OpenSSL/Mbed TLS, zlib/zstd)
and against its own CPU/GPU execution modes.

There is exactly one such pipeline. If you are about to add a second differential framework,
stop — absorb it into this one instead. Glossary terms for this program (Boundary,
Independence Group, Relation, Execution Receipt, GPU Gate, Vacuity, Conversion Loss):
`doc/glossary.md`. Writing a new counterpart spec: `.claude/skills/spipe.md` §
"Writing a Simple Counterparts Compare Test".

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

**Wave 0 and Wave 1 complete.** 138/138 examples green across nine specs, all measured with
`bin/simple run` (the daemon path trips the 800-module cap):

| spec | result |
|---|---|
| contract_model | 18/18 |
| converter_graph | 19/19 |
| relation_matrix | 19/19 |
| evidence_projection | 6/6 |
| counterpart_abi | 8/8 |
| provider_registry | 19/19 |
| package_registry | 19/19 |
| foundation_redteam | 21/21 |
| worker_isolation | 9/9 |

Landed lanes: F1 ABI + mock adapter, F2 package resolver + `counterpart` CLI, F3 isolated
worker with proven crash containment, F4 provider registry/runner, F5/F6 converter graph +
N-way relation engine, F7/F8 artifact store + evidence/manual projection, F9 adversarial
red-team.

Not started: all of Waves 2–7 — no real upstream provider exists yet. Wave 2 (mock, zlib,
HarfBuzz, OpenSSL pilots) is the production-readiness gate; Chrome and Venus must not start
until it passes.

### Carry these forward

- **The native-build wiring is UNVERIFIED.** The ABI works on the interpreter path only.
  Proving the native path needs a native build of an `rt_counterpart_*` caller, which the
  Stage-3 self-host blocker prevents.
- **`bin/simple` is a Rust seed**, so every number above is seed-attributed, and
  `bin/simple counterpart …` is unreachable — use `bin/simple run src/app/counterpart/main.spl`.
- **SBOM emission is not implemented**; `sbom_sha256` is parsed and placeholder-checked only.
- **The mock lock record is all `pending`**, so `verify`/`run` correctly exit 1 as UNVERIFIED.
- Three fail-open defects were found and fixed during Wave 1 — artifact hashing that made
  every binary verify against every other, a missing derived-expected-value gate, and a
  hardcoded `ConversionLoss.identity` that made the exactness gate dead code on the
  production path. Expect more of this shape; sabotage every guard you add.

## Current state addendum (2026-08-15)

- **First real upstream provider landed: Chrome.**
  `src/lib/nogc_sync_mut/spec/evidence/counterpart/chrome_dom_snapshot_provider.spl`
  drives real Chrome over the pure-Simple CDP client at boundary
  `chrome.dom_snapshot@1`. Spec:
  `test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl` (green).
  Run: `SIMPLE_TIMEOUT_SECONDS=600 bin/simple run test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl`
  (still `run`, not the daemon — 800-module cap note above holds).
- **Branch coverage closed to 100% recordable** across the counterpart
  library. Evidence and per-file table:
  `doc/08_tracking/test/counterpart_branch_coverage_closure_2026-08-15.md`.
  Coverage only records under `SIMPLE_COVERAGE=1`, and "recordable" is the
  honest ceiling — the collector skips `pub val` initializers, match heads,
  and struct-method decisions (bugs
  `coverage_collector_skips_pub_val_and_match_heads_2026-08-15.md`,
  `coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md`).
- Related same-session lanes on the browser side (vector-font differential
  vs Chrome, docker+vulkan browser lane): see the
  [browser feature expert](../browser/skill.md) 2026-08-15 handoff.

## Related feature experts applying this methodology

- [board_vulkan](../board_vulkan/skill.md) — applies the same real-executed-counterpart /
  independence-group discipline to a SimpleOS board-Vulkan boundary-comparison harness
  (device enumeration, SPIR-V, command-stream, readback). Not a second pipeline — it reuses
  this feature's vocabulary and traps (independence_group over provider count, unavailable
  is never PASS, canonicalize by explicit rule not heuristic).

## Update Rule

Update this file in the same change as any counterpart work: new links, new constraints
discovered, and the current-state section above.
