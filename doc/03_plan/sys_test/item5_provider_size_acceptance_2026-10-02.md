# Item 5 concrete runtime acceptance and TDD plan

## Variation acceptance extension — 2026-10-11

Retain I5-01..I5-14 unchanged. The following rows extend their production scenarios for selected REQ-016..023; **new or extended executable coverage is pending**, not PASS. Add cases under the existing canonical test owners, with generated manuals under `doc/06_spec`; never place executable specs in that documentation tree.

| Case | Requirement / existing cases | Required observable assertion |
|---|---|---|
| I5-V01 | REQ-016; I5-03/04/14 | Existing registry/schema owner admits compatible descriptors, rejects unknown required IDs/versions, and prevents stale-generation use without duplicate state owners. |
| I5-V02 | REQ-017; I5-04/08/14 | Resolver selects one scoped overlay, rejects unrelated shadowing, gives legacy aliases the same decision, and invalidates only affected selected-source cache projections. |
| I5-V03 | REQ-018; I5-03/07 | Cross-target emission does not inherit host CPUID; missing OS state, wrong ABI/width/endian, weaker worker domains and device-generation changes reject before unsafe execution. |
| I5-V04 | REQ-019; I5-07 | Scalar versus AVX2/AVX512/NEON/SVE/SVE2/RVV compare tails, masks, aliasing, alignment and numerical edge cases; exact instruction evidence defeats width-only false positives. |
| I5-V05 | REQ-020; I5-05/10 | Actual async submit/result/wake and sync adapter share operation identity; cancel/timeout retains buffers until native retirement; live pins prevent unload; duplicate completion is rejected. |
| I5-V06 | REQ-021; I5-01/02/11/12 | No-demand remains zero-load; repeated prepared SIMD calls perform no probes/discovery/ring submissions; actual DB/HTTP matched cohorts retain equal workloads, results, raw samples and RSS. |
| I5-V07 | REQ-022; I5-02/03/07 | Real compiled GPU artifact and actual device submit/readback have separate receipts; CUDA-off remains CPU-capable; incompatible/missing providers fail consistently; no duplicate device manager. |
| I5-V08 | REQ-023; I5-07/13/14 | Real caller switches to the admitted provider, parity and rollback pass, old semantic body is removed or a bounded facade, and runtime claim matches its exact target/provider generation. |

Emulation can establish functional target execution and ISA refusal, not physical-device performance. Host C CUDA device tests cannot certify the environment-variant GPU bridge, SOSIX-G or Simple applications. Retain 30 development / 100 release matched samples and all original size/startup targets; no new numerical budgets are inferred from the proposal. Record feature/target/OS/ABI/vector-state/backend axes on existing trace rows.

Mandatory subcases within these eight rows:

- V01/V03: frozen V1 versus exact V2 feature-word rejection; missing ARM32/x86-32/RV32 and non-Linux target registrations; codec round trips; checked 32-bit pointer conversion; SVE VL and RVV VLEN/SEW/LMUL/enablement changes across worker migration.
- V04: overflow and trap behavior, write/effect ordering, guard-page masked tails, zero/merge/agnostic inactive lanes, duplicate scatter destinations, NaN/signed-zero/reduction order and unsupported hard requirements with failing driver exit.
- V05/V07: device loss and uncertain partial effects forbid blind CPU replay; require-GPU/direct-required requests refuse unavailable execution. Scratch-output fallback is legal only when effects are isolated and prior native access has retired. Verify retained input/output leases and no premature publication.
- V06/V08: final bootstrap/compiler/core/lib/MCP/LSP and real app gates bind the actual producer; no source-only marker, cross-link or C microbenchmark substitutes for application execution or physical-target performance.

Status: planned, not executed. Requirements remain the user-selected 2026-09-02
contract; no budgets or supported hosts are removed.

Each executable SSpec scenario uses step descriptions, REQ/NFR tags, real
production calls and built-in matchers. Source substring checks are auxiliary
architecture checks. Missing native artifacts or receipts block acceptance.
Existing synthetic BS7 receipts verify their checker only.

| Case | Requirement | Setup, action and observable assertion |
|---|---|---|
| I5-01 | REQ-001, NFR-005 | Start no-import hello with loader/init counters; register all optional descriptors; assert zero mappings, initializations, archive reads and provider effects before demand. |
| I5-02 | REQ-002, REQ-015 | Install sealed precompiled provider; demand a capability; assert exactly one admitted load/init, expected output and no source parse; repeat demand and assert reuse. |
| I5-03 | REQ-002, REQ-012 | Mutate missing artifact, digest, ABI, target, architecture, dependency and policy independently; assert exact typed error and zero initialization/effects. |
| I5-04 | REQ-002 | Supply coherent image/receipt digests but mismatched pinned member identity/extent/checksum; reject archive authority before publication. Include archive-size bounds. |
| I5-05 | REQ-002 | Concurrent first demand with bounded synchronization; assert one initializer, identical admitted identity, no partial receipt, stable cached refusal on failed initialization. |
| I5-06 | REQ-004, REQ-005 | Exercise pure and foreign selection and rollback; effectful fixture records one write per request. Shadow comparisons execute only admitted pure bounded operations. |
| I5-07 | REQ-006, REQ-011, NFR-006 | Run actual parity/failure/mutation/resource fixtures for each retained provider family and supported target; assert same results/errors and no unrelated provider dependency. |
| I5-08 | REQ-003, REQ-007, REQ-013 | Link NoGC no-allocation hello; inspect map, sections, constructors, exports and dynamic dependencies; assert no collector/compiler/backend/optional roots and a reason for every retained root. |
| I5-09 | REQ-008, REQ-009, REQ-010 | Compare release-small, ordinary release and debug; prove omitted unwind/RTTI/exceptions unnecessary; demand an exception-requiring foreign provider and assert base size/roots unchanged and functionality retained. |
| I5-10 | REQ-011, REQ-012 | Hold live provider pin then request close; assert refusal; release pin and close; assert later invocation rejected. Do not require OS unmapping immediately after close. |
| I5-11 | REQ-014, NFR-001..003 | Replay exact captured link and strip inputs for Simple/C same-output hello; verify artifact hashes and size limits, with admitted non-ELF allowance. Retain unstripped/stripped bytes and inspection products. |
| I5-12 | NFR-004, NFR-007 | Collect matched same-host Python/Simple startup and peak RSS: at least 30 development or 100 release samples, p50/p95, binary/toolchain/source hashes. Reject stale or synthetic cohorts. |
| I5-13 | REQ-003, REQ-015 | Invoke packaged CLI optional command; observe compiled-artifact demand boundary, then exercise unavailable provider; assert no raw-source fallback and no eager Office/UI/GPU roots in minimal command. |
| I5-14 | item 5 layering | Inspect and exercise kernel/driver versus extension ownership; retain existing owner-result/provider interfaces, no unsolicited ECS/MDSOC+ kernel conversion. |

## Bounded sequence

1. Discover admitted runtime and record its immutable identity. Add a behavioral
   regression for the pinned-member authority seam, observe RED, implement the
   minimal validation in its owner, then observe GREEN once.
2. Extend actual loading/target/policy and lifetime coverage around the existing
   src/os/smf/provider_loader.spl; do not create a competing loader.
3. Implement exact link closure, provider packaging and CLI cutover with separate
   isolated ownership. RuntimeFeatureClosureV1 must be proven in current source,
   not inferred from a historical document.
4. Build real size/startup cohorts and cross-host qualification evidence. Run
   required core/MCP/LSP checks once after relevant changes and update manuals
   from executable specs. At most three fix/verification cycles per feature.

Acceptance ledger records source/head/target, fixture hashes, command, exit,
assertion result, evidence path and remaining blockers per case. No helper PASS,
source-token match or metadata-only receipt certifies native execution.
