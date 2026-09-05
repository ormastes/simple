# Counterpart Conformance Infrastructure — Parallel Agent Plan

Date: 2026-08-09
Design: `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`

Sequencing decision that governs everything below: **prove the generic infrastructure with
zlib, HarfBuzz and a small crypto subset before attaching Chrome and SimpleOS.** Otherwise
browser, GPU, QEMU and converter defects mix and no failure can be attributed to the framework
or to the domain implementation.

## Wave 0 — contract freeze and audit

| Agent | Ownership | Deliverables | Exit gate |
|---|---|---|---|
| A0 Architecture captain | ADRs, shared names, merge order | Final boundary-ID syntax, ABI v1, manifest schemas, locked-file list | All other agents can implement without changing core contracts |
| A1 Repository differential audit | Existing web/layout/GPU/crypto/compress tools | Complete inventory; reuse/delete/wrap decision per tool | No unclassified comparison implementation |
| A2 External provider audit | Upstream versions, build systems, licenses | Provider matrix, pinned revisions, license/SBOM policy | ≥1 viable provider per pilot domain |
| A3 Boundary/schema catalog | Web, Vulkan, crypto, compression schemas | Input/output schemas + correspondence classification | Every pilot boundary marked exact, semantic or non-corresponding |
| A4 Modern SSpec migration audit | Current specs and sidecars | Migration ledger, scenario IDs, legacy assertions, evidence paths | Initial migration set selected |
| A5 Red-team design | Vacuity, common-mode failure, converter loss, hostile adapters | Threat model and sabotage catalogue | Each foundation lane has ≥1 required negative test |

Locked during Wave 0 (changes afterwards need an A0 ADR amendment):

```
src/lib/common/spec/evidence/model.spl
counterpart ABI header
boundary ID format
manifest schemas
conversion loss enum
```

## Wave 1 — foundation

| Agent | Ownership | Deps | Deliverables |
|---|---|---|---|
| F1 Native ABI | C header, runtime shim, Simple wrapper | A0 | load, manifest, open, invoke, reset, close |
| F2 Package/build resolver | Lockfile, source verification, cache, SBOM | A2 | Reproducible mock-provider build |
| F3 Isolated worker | Framing, budgets, crash/timeout handling | F1 | Worker survives adapter crash, reports typed failure |
| F4 Provider registry | Descriptor loading, capability selection | F1, F2 | In-process, worker and process providers share one interface |
| F5 Converter graph | Schema routing, loss enforcement, receipts | A3 | Exact-through-lossy route is rejected |
| F6 Relation engine | N-way matrix, domain-neutral relations | F5 | exact, structural, cross-decode, invariant, image |
| F7 Artifact/provenance store | Content addressing, manifests, retention | F2 | Raw/canonical artifacts and receipts have stable hashes |
| F8 Modern SSpec integration | Provider, evidence projection, manual blocks | F4, F6, F7 | One real provider run appears in a generated QA manual |
| F9 Foundation red-team | Mutation and vacuity suite | F1–F8 | Crash, zero comparisons, fake hash, missing provider, lossy route all fail |

Merge order: `F1/F2/F5/F7 → F3/F4 → F6 → F8 → F9`.

## Wave 2 — stable pilot providers (production-readiness gate)

Do not begin with Chrome or Venus.

| Agent | Pilot | Purpose | Acceptance |
|---|---|---|---|
| P1 Mock provider | echo/hash/error/crash components | Exercise every ABI and worker path | All foundation negatives proven |
| P2 DEFLATE provider | zlib + libdeflate | Cross-decode and non-byte-exact relations | Full encoder/decoder matrix + corruption tests |
| P3 HarfBuzz provider | shaping component | Structural alignment, UTF offset conversion | Glyph/cluster/advance corpus with mutation |
| P4 OpenSSL provider | SHA-256, AES-GCM | Vector authority, secret redaction, typed errors | NIST/RFC vectors plus tamper cases |
| P5 Pilot SSpec/manuals | all four pilots | Validate evidence and generated documentation | Each pilot has user and QA projections |

Chrome, QEMU and full GPU work do not proceed until Wave 2 passes.

## Wave 3 — web renderer

| Agent | Deliverables |
|---|---|
| W1 Chrome adapter | Wrap existing CDP scripts, pin Chrome/protocol, structured unavailable state |
| W2 DOM/style schemas | Canonical NodeArena and ComputedStyleTable converters |
| W3 Layout converter | Geometry, line grouping, UTF-16/UTF-8 resolution, current tolerance rules |
| W4 Shaping integration | Simple CPU/GPU shaping vs HarfBuzz |
| W5 Draw IR parity | CPU/GPU canonical Draw IR, stable ordering |
| W6 Raster/readback | CPU/GPU exact profile, hosted browser supplemental profile |
| W7 WPT corpus | Import selection, preprocessing ledger, minimized regressions |
| W8 Web migration | Modernize two existing Chrome specs; dual-run then retire shell parsing |

W1 wraps current scripts without touching renderer production code. W2–W6 add observation ports
only where current extraction is insufficient.

## Wave 4 — Vulkan and SimpleOS

| Agent | Deliverables |
|---|---|
| V1 SPIR-V providers | SPIRV-Tools/SPIRV-Cross validation and reflection |
| V2 Vulkan layer capture | Test-only Vulkan layer, normalized command semantics |
| V3 Software ICD providers | SwiftShader and optional lavapipe execution/readback |
| V4 Venus host bridge | virglrenderer/vtest provider, protocol projection |
| V5 QEMU guest bridge | x86-64, AArch64, RISC-V SimpleOS profiles |
| V6 GPU receipts | Submission, fence, readback, fallback, device identity |
| V7 CTS integration | Selected dEQP/VK-GL-CTS shards, result projection |
| V8 Vulkan migration | Replace planned GPU-only comparator verdicts with Modern SSpec evidence |
| V9 Vulkan red-team | Handle-map mutation, dropped event, fake readback, CPU fallback, missing fence |

V2/V3/V4 run in parallel once the trace schema is frozen. V5 depends on V4. V8 depends on V2–V7.

Board rule applies: a QEMU-only Venus/SimpleOS result is a defect, not a completion — keep the
physical-board build/boot/run path documented, or file the blocker explicitly
(`.claude/rules/board-runnable.md`).

## Wave 5 — crypto and compression breadth

| Agent | Ownership |
|---|---|
| K1 | Vector import: NIST ACVP/CAVP and RFC vector adapters |
| K2 | OpenSSL breadth: digest, MAC, cipher, AEAD, KDF, signatures |
| K3 | Mbed TLS/PSA breadth: independent overlapping algorithm set |
| K4 | PQ providers: ML-KEM/ML-DSA where applicable |
| K5 | Mode parity: scalar/SIMD/GPU relations and execution receipts |
| Z1 | zlib/libdeflate: DEFLATE, zlib, gzip |
| Z2 | zstd: frames, dictionaries, streaming, corruption |
| Z3 | LZ4/Snappy: block/frame and streaming |
| Z4 | Brotli/XZ: Brotli and LZMA2/XZ |
| Z5 | Resource safety: expansion limits, malformed entropy, timeouts |
| M-ALG | Convert the existing cipher/compression gate to structured plans |

Each algorithm agent adds provider descriptors and domain plans under its own directory and must
not edit central registries directly.

## Wave 6 — spec-to-sspec and MDSOC+ refactoring

| Agent | Deliverables |
|---|---|
| M1 | SSpec semantic parser: stable scenario/assertion/source-span model |
| M2 | Explicit evidence binder: `bind-evidence` and no-fabrication verification |
| M3 | Web observation ports: immutable snapshots at corresponding boundaries |
| M4 | Vulkan observation ports: trace/readback ports without foreign imports |
| M5 | Crypto/compress observation ports: common request/result contracts across modes |
| M6 | Legacy retirement: dual-run reports and deletion eligibility |
| M7 | Documentation: architecture, provider authoring, converter authoring, migration, troubleshooting |

## Wave 7 — hardening

| Agent | Focus |
|---|---|
| H1 | Reproducibility: source-build equivalence, prebuilt verification, cache poisoning |
| H2 | Sanitizers/fuzzing: ABI, adapters, converters, framed worker protocol |
| H3 | Determinism: locale, timezone, fonts, seeds, stable ordering, hashes |
| H4 | Security: secret handling, untrusted fixtures, sandboxing, permissions |
| H5 | Licensing: SPDX, notices, redistribution restrictions, SBOM completeness |
| H6 | Performance: session-level loading, converter caching, bounded artifact retention |
| H7 | Final red-team: common-mode failures, false independence, vacuity, fallback spoofing |

## Migration sequence (applies per domain)

- **M0 inventory** — classify each differential spec: `legacy-shell`, `wrapped-provider`,
  `typed-evidence`, `native-counterpart`, `rejected-or-noncorresponding`.
- **M1 wrap without semantic change** — wrap existing Chrome and layout tools as process-backed
  adapters, preserving current normalization and verdict behavior exactly. First targets:
  `test/system/web_engine_chrome_component_differential_spec.spl`,
  `test/03_system/browser_engine/chrome_layout_differential_spec.spl`.
- **M2 dual-run** — legacy tool and new pipeline per fixture. Assert same comparison count, same
  paired-node count, same mismatch classification, same worst mismatch, same unavailable
  behavior, same failure under sabotage.
- **M3 typed evidence** — replace shell-summary parsing with `CounterpartEvidenceProvider` and
  Modern SSpec oracles.
- **M4 native boundary ports** — move extraction from standalone scripts into stable production
  observation ports where that improves fidelity without adding test dependencies.
- **M5 retire legacy** — delete a legacy differ only after ≥2 releases of dual-run parity, all
  retained baselines migrated, the generated manual current, and sabotage proving the new path
  detects a real mutation.

Order of domains after web: cipher/compression gate → host Vulkan software lane → SimpleOS
Venus/QEMU lane → broader web CPU/GPU stage parity.

## Agent execution rules

Every lane must:

1. Own a disjoint path set.
2. Consume frozen shared interfaces.
3. Add unit tests for its own parser/converter/adapter.
4. Add ≥1 real integration case.
5. Add a sabotage that turns green to red.
6. Restore and demonstrate green again.
7. Emit raw and canonical artifact hashes.
8. Update the relevant design or guide.
9. Add a descriptor rather than editing central registry files.
10. Never report unavailable as pass.
11. Never create expected output from actual candidate output.
12. Never weaken an existing exact oracle without a reviewed relation change.

The merge captain rejects any lane that only proves "the adapter ran." Every lane must prove a
deliberately incorrect result is rejected.

## CI matrix

| Tier | Providers | Purpose |
|---|---|---|
| 0 | Mock providers only | ABI and converter unit tests |
| 1 | Verified prebuilt zlib, HarfBuzz, OpenSSL | Fast portable integration |
| 2 | Source-built reference packages | Reproducibility |
| 3 | Pinned Chrome/Servo | Web stage conformance |
| 4 | SwiftShader/lavapipe | Deterministic Vulkan reference |
| 5 | Host hardware GPU | Real GPU execution and fallback detection |
| 6 | SimpleOS QEMU/Venus, three architectures | Driver and transport |
| 7 | Physical boards/GPUs | Hardware release gate |
| 8 | Sanitizer/fuzz workers | Hostile-input hardening |

Normative correctness must not depend only on hardware or a flaky hosted browser lane. Hardware
lanes prove real execution and environment compatibility; portable references and vectors carry
the stable correctness gate.

## First pull-request sequence

1. ADR and frozen contracts — boundary IDs, manifests, conversion loss, provider kinds.
2. Mock adapter and dedicated ABI runtime shim — manifest, invoke, reset, crash, malformed result.
3. Isolated worker and artifact store — timeouts, output bounds, content-addressed receipts.
4. Converter graph and N-way relation engine — including the exact-through-lossy negative test.
5. Modern SSpec provider and manual projection — one generated manual backed by a real invocation.
6. zlib/libdeflate pilot — first complete cross-encode/decode matrix.
7. HarfBuzz shaping pilot — first structural and offset-space conversion.
8. OpenSSL AES-GCM/SHA pilot — first normative-vector and secret-redaction profile.
9. Chrome wrapper migration — preserve current DOM/style/layout results before refactoring.
10. Simple CPU/GPU web parity — Draw IR, logical hash, execution receipt.
11. SwiftShader/lavapipe Vulkan profile — host deterministic Vulkan execution.
12. Venus vtest and QEMU profiles — full transport, fence and readback evidence.
13. spec-to-sspec semantic evidence binding — migrate web, Vulkan and algorithm specs.
