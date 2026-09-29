<!-- codex-research -->
# Simple Platform Unification — Non-Functional Requirements

**Date:** 2026-09-13
**Status:** selected measurable requirements; evidence remains incomplete

Inherited `PF/NFR-001..007`, `EODL/NFR-001..012`, and
`SMPB/NFR-SMPB-001..004` remain normative. Where thresholds overlap, the
stricter gate applies; notably the EODL 1.15x pilot result does not qualify a
parser backend for PF's 1.5x `auto` promotion gate.

## Requirements

- **NFR-001 — Semantic parity.** On the retained acceptance corpus, every
  promoted parser backend shall produce identical ordered tokens, regions,
  syntax/actions/HIR, source mappings, diagnostics, invalidation, deterministic
  receipt fields, and semantic hash. Backend/fallback/timing provenance may
  differ but shall be excluded from semantic equality.

- **NFR-002 — Parser memory.** Canonical multifile peak parser RSS shall be at
  most 50% of the retained pre-change baseline. Completed-stage arenas shall
  show no monotonic retained growth, and disabled `TagDemand` shall report zero
  tag/index allocations.

- **NFR-003 — Parser latency and promotion.** Median canonical scalar time shall
  be no more than 110% of the legacy scalar oracle. A SIMD or GPU stage/size
  class becomes eligible for `auto` only at at least 1.5x median end-to-end
  speedup over scalar. GPU time includes transfer, launch, synchronization, and
  ordered materialization. For edits touching at most 1% of source bytes,
  median incremental latency shall be at most 25% of clean full-reparse latency.

- **NFR-004 — Variant selection latency.** On the named reference catalog,
  selection p95 shall be no greater than 1 ms warm and 25 ms cold. Evidence
  shall separate discovery, admission, selection, mapping, and first execution.

- **NFR-005 — Dispatch overhead.** A generation-pinned dense provider batch
  dispatch shall add no more than 2% over the direct reference batch call and
  perform no per-element allocation, filesystem scan, environment parse,
  symbol lookup, process spawn, or lifecycle lock.

- **NFR-006 — Provider performance and memory.** At least one declared pilot
  workload shall demonstrate 1.15x speedup over its qualified reference.
  Selecting one optimized provider shall increase steady-state max RSS by no
  more than 5%; when none is selected, catalog infrastructure shall add no more
  than 2 MiB resident memory.

- **NFR-007 — Determinism and reproducibility.** Identical source, grammar,
  environment, target registry, catalog, policy, dependency lock, machine spec,
  artifacts, and valid calibration evidence shall yield byte-identical semantic
  caches/manifests and identical binding/plan digests. A release-evidence
  instance may additionally bind unique run/session IDs, timestamps, logs, and
  timing; its shared execution-binding digest shall be deterministic over the
  declared semantic inputs, while the full instance digest shall authenticate
  those run-specific fields. Receipts shall record exact revision, binary,
  fixture, owner generation, and input digests.

- **NFR-008 — Bounds and overflow safety.** Source/token/region/arena counts,
  catalog bytes/records/depth, rejection records, sessions, queues, process
  capture, image entries/bytes, machine devices/argv, evidence steps, and all
  count/offset arithmetic shall have explicit finite limits. Exact-fit values
  shall succeed; mathematical overflow and over-capacity input shall fail before
  allocation, mapping, launch, or publication.

- **NFR-009 — Security and fail-closed admission.** Across supported fixtures
  there shall be zero wrong-ISA execution, host-to-target feature leakage,
  publication-before-admission, silent required fallback, digest-substitution,
  path/argv/environment injection, replay acceptance, use-after-retire, or
  promotion of mutated candidate bytes. Trust and compatibility checks precede
  executable mapping whenever inert metadata permits.

- **NFR-010 — Lifecycle and progress.** Provider replacement shall preserve
  generation pins until CPU calls, sessions, callbacks, JIT references, device
  work, buffers, and completion objects drain. Process input/output handling
  shall make bounded concurrent progress without pipe deadlock; timeout,
  cancellation, short write, overflow, child exit, and reap failure shall end in
  explicit non-authoritative receipts with no live lease or leaked resource.

- **NFR-011 — Baseline and startup isolation.** Every supported image profile
  shall cold-boot with optional optimized providers absent or quarantined.
  CPU-only help/version/reference compilation shall not initialize optional GPU
  services. Startup evidence shall report cold/warm latency, mapped text, max
  RSS, and initialized provider/service set.

- **NFR-012 — Hot-path discipline.** Parser requests, provider dispatch, loader
  lookup, module resolution, and VM-control requests shall not repeatedly scan
  full trees, rediscover executables/firmware, parse environment/configuration,
  spawn discovery processes, or reread unchanged manifests. Caches shall have
  bounded cardinality and explicit invalidation by environment, policy,
  registry, catalog, artifact, executable, firmware, or machine-spec identity.

- **NFR-013 — Build portability.** Static target lookup shall be in-process and
  data-driven. Adding a guest architecture shall require one canonical catalog
  entry and, only when required, one target stanza/provider implementation.
  Hosted/guest distinctions, target triple, ISA/ABI/float policy, and boot
  sources shall be test-covered and unambiguous in documentation.

- **NFR-014 — Release evidence integrity.** A qualification run shall retain
  immutable candidate digest, derived writable-state identity, firmware/QEMU/
  accelerator identity, cold-boot and reboot session identities, ordered guest
  operation receipts, before/after persistence identities, bounded stdout/
  stderr/log captures, and terminal status. Reuse-mode, source-only, seed-only,
  synthetic, or emulated evidence shall never be relabeled as live native proof.

- **NFR-015 — Measurement quality.** Performance evidence shall name fixture,
  machine/backend/device, warm/cold classification, repetitions and warmup,
  p50/p95/p99, max RSS/device memory, allocation counters, raw-sample location,
  crossover decision, and parity status. Tiny, medium, large, Unicode-heavy,
  malformed, and relevant SIMD-tail inputs shall be represented. Missing hosts
  or devices remain explicit unsupported or `MissingEvidence` rows.

- **NFR-016 — Verification quality.** Each acceptance criterion shall be checked
  at most once unchanged per session and no feature shall exceed three distinct
  fix/verify cycles. Completion requires no placeholder/stub assertions,
  executable/generated `.spl` specs anywhere under `doc/06_spec`, direct runtime-boundary
  violations, unresolved requirement trace, P0/P1 review defect, or stale
  operator documentation. The final verifier shall report PASS against the exact
  admitted artifacts; a narrow source check cannot substitute for that verdict.

## Verification matrix

| NFR | Required measurement/evidence | Current status |
|---|---|---|
| NFR-001..003 | Forced legacy/scalar/SIMD/GPU corpus plus retained parser benchmark/RSS/allocation and incremental/full receipts | PF specs/plans exist; unified admitted execution incomplete |
| NFR-004..006 | EODL reference catalog benchmarks and direct-vs-dispatch comparison with retained raw samples | EODL authority exists; production qualification incomplete |
| NFR-007..010 | Pinned canonical vectors; exact-fit/overflow, tamper, policy, process-progress, generation-drain, and replay tests | Several source contract tests exist; full production-owner evidence incomplete |
| NFR-011..014 | Profile build matrix; baseline cold boot; sealed-plan inspection; immutable candidate, live guest, reboot/persistence manifest | Planned in `doc/03_plan/sys_test/simple_platform_unification.md`; live release chain missing |
| NFR-015 | Qualified benchmark manifests containing all declared fields and unsupported rows | Missing consolidated admitted evidence |
| NFR-016 | Verify transcript, must-check ledger, generated-manual inspection, direct-env guards, final Astra review | In progress; no final PASS claimed |

Boot-to-ready and guest round-trip numeric budgets are not invented here: the
current system-test plan records them as pending explicit selection. Their
absence does not relax correctness, integrity, or cold-boot requirements, but
it prevents claiming those latency dimensions are fully specified.
