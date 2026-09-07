# Two-Plan and REQ-KPF Independent Completion Audit

**Date:** 2026-09-03  
**Audited head:** `2c2aa2987d3`  
**Verdict:** **FAIL — implementation is materially advanced but not complete**

This audit compares the current tree with every M0–M5 gate in
`macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`, every
Phase 0–8 gate in `kernel_plugin_migration_plan.md`, and REQ-KPF-001..012.
Structural, focused executable, native-product, and external-authority evidence
are kept separate. No structural test is counted as native bootstrap, native
cross-architecture, signing, notarization, or production-cutover evidence.

## Freshly Rechecked Evidence

- KPF acceptance: **5/5 PASS** on the admitted macOS arm64 runtime.
- K0g closure scenario: **2/2 PASS**.
- Cross-placement lifecycle/crash policy: **4/4 PASS**.
- Canonical schema: **10/10 PASS**; shared malformed ABI corpus **1/1 PASS**.
- Worker-wire generation/bounds: **3/3** and **4/4 PASS**.
- Generated lint catalog: **2/2 PASS**.
- Lint table, including remove-row behavior: **10/10 PASS**.
- Extended-enum KPF closure: **11/11 PASS**; source mutation checker PASS.
- MDSOC++ sealer: **5/5 PASS**.
- M2/M3 source mutation matrix: **16/16 rejected**.
- M4 portable contract: **PASS**.
- The aggregate Phase 0–8 checker failed closed before Phase 1 because its
  default runtime selector admitted no runtime. This is not a phase PASS.
- The M5 mutation run completed in the aggregate process, but its output was
  not retained by the caller timeout; this audit relies only on the existing
  retained 5/5 mutation receipt and does not claim a fresh rerun.

The current tree also includes the latest worker-wire projection, shared
malformed ABI corpus, generated lint catalog and typed edits, enum sealer,
browser/Wasm degraded-capability parity, centralized temporary cleanup,
build-progress summary, compiler-context memory reduction, and LLVM temporary
artifact cleanup.

## macOS M0–M5

| Milestone | Source/portable status | Native/release status |
|---|---|---|
| M0 baselines/receipts | Receipt framing and live-byte validation implemented | **BLOCKED:** no admitted arm64 and x86_64 Phase2/3 baseline pairs |
| M1 target/linker | Darwin key, SDK/deployment, Mach-O and linker-policy checks implemented | **BLOCKED:** no retained two-architecture native proof |
| M2 projection receipts | Ten families, immutable generations, fallback attribution and 16/16 mutation rejection pass | **BLOCKED:** no causal native incremental receipts |
| M3 Phase2→3 reuse | Separate caches, immutable compatibility manifest, no-follow admission and attributed ledgers implemented | **BLOCKED:** no producer-authenticated native chain, no native clean/reuse equivalence, no native zero-work no-op receipt |
| M4 per-architecture | Exact fixture/tool/provider/parser contract passes | **BLOCKED:** neither arm64 nor x86_64 has a qualifying native M4 receipt |
| M5 universal promotion | Hermetic three-file snapshot and retained 5/5 mutation evidence exist | **BLOCKED:** no admitted thin pair, dual-native execution, signing, notarization, stapling, Gatekeeper or digest-preserving promotion |

No isolated remaining M0–M5 source defect was found. The exact unavailable
producer tuple remains:

```text
src/compiler_rust/target/bootstrap/simple
src/compiler_rust/target/bootstrap/libsimple_native_all.a
src/compiler_rust/target/bootstrap/libsimple_compiler_backfill.a
```

The host reports zero valid code-signing identities. No Intel-native runner or
artifact and no valid notary profile are present.

## Compiler Plugin Phases 0–8

| Phase | Determination | Missing acceptance authority |
|---|---|---|
| 0 partition | Structural PASS; closure is fail-closed | aggregate executable matrix did not admit its runtime |
| 1 ABI digest | Focused executable PASS retained | full ordered matrix cannot complete under the aggregate runtime selector |
| 2 param objects/lint | Focused executable PASS retained | same aggregate runtime blocker |
| 3 manifest identity | Structural/focused PASS | startup/native product admission remains unqualified |
| 4 lint table | **Focused executable PASS, including remove-row 10/10** | ordered whole-plan matrix remains blocked |
| 5 backend relocation | Structural PASS | LLVM+Cranelift native bootstrap parity and Stage2/3 receipt absent |
| 6 APK/SFFI negotiation | Structural and native ABI matrix PASS | original product admission/SPipe row lacks admitted product runtime |
| 7 APK-only closure | Structural policy PASS | one-binary, dynload, backend parity, startup, architecture RSS and growth rows remain unqualified |
| 8 package ranges | Source-contract PASS | executable lock/update matrix is blocked by Phase 7 ordering and runtime authority |

The selected LLVM+Cranelift, ABI-v1, `simple.sdn`, atomic APK-only policy has
not drifted. Phase 7 is the ordering barrier; Phase 8 cannot be declared done
before it.

## REQ-KPF-001..012

| Requirement | Determination |
|---|---|
| REQ-KPF-001 placement parity | **Partial:** lifecycle parity passes; one shared semantic conformance corpus across static/native/worker/Wasm product placements remains absent |
| REQ-KPF-002 K0g closure | **PASS for source closure:** focused scenario passes; native bootstrap qualification is separate |
| REQ-KPF-003 SCI/query authority | **Partial:** adapters preserve SCI/query admission; end-to-end product proof that runtime never searches/builds a missing provider remains open |
| REQ-KPF-004 stable ABI | **Focused PASS:** canonical four-language malformed/layout corpus and native projections pass |
| REQ-KPF-005 bounded/noalloc | **Partial:** focused allocation and bounded-capacity evidence exists; long-run production-path noallocation proof remains open |
| REQ-KPF-006 dense O(1) dispatch | **Focused PASS:** lookup/scaling and fixed-capacity benchmark gate passes; product qualification remains open |
| REQ-KPF-007 lifecycle safety | **Focused PASS:** stale handles, unload, rollback, cancellation, crash policy and placement lifecycle evidence pass |
| REQ-KPF-008 generated projections | **Focused PASS:** Simple/C/Rust/C++, WIT, worker wire, deterministic generation and malformed corpus exist |
| REQ-KPF-009 lint truth | **Partial:** coverage/verdict/catalog/edit evidence passes; authoritative rust-analyzer plus clangd/clang-tidy product sessions and full mixed-workspace qualification remain open |
| REQ-KPF-010 shared IDE tooling | **Partial:** tooling sessions and typed authoritative/degraded browser receipt exist; native/desktop/browser production cutover and shared live-client conformance remain open |
| REQ-KPF-011 extended enums | **Focused PASS:** operation completeness, dense tags and critical `Dyn` rejection pass mutation-sensitive tests |
| REQ-KPF-012 MDSOC++ | **Partial:** deterministic sealer and IDE/tooling pilot pass focused tests; real product upgrade, state migration, publication, rollback and drain proof remains open |

## Actionable Source/Product Gaps

More than one independent gap exists, so this audit deliberately implements no
arbitrary single subset:

1. Add one semantic cross-placement conformance corpus that executes equivalent
   static, native, worker and optional Wasm providers (REQ-KPF-001/003).
2. Add long-run product-path noallocation/capacity evidence rather than only the
   focused allocator probe (REQ-KPF-005).
3. Finish authoritative Rust and C++ IDE sessions: rust-analyzer and
   clangd/clang-tidy lifecycle, exact toolchain/build receipts, cancellation,
   and stale-publication behavior (REQ-KPF-009/010).
4. Cut native IDE, VS Code desktop, and browser/Wasm clients over to one live
   canonical conformance corpus; the macOS VS Code host remains blocked before
   activation by its overlong IPC socket path (REQ-KPF-010).
5. Execute an MDSOC++ product generation upgrade with state migration, atomic
   publication, draining, rollback and retained receipts (REQ-KPF-012).
6. Complete the Phase 7 one-binary/dynload/startup/RSS product matrix before
   executing and accepting Phase 8.

## Runtime and External Authority Gaps

- producer-authenticated Stage2 runtime and archive tuple;
- admitted arm64 Phase2→3 and M4 artifacts plus architecture RSS baseline;
- native x86_64 runner, compiler, artifacts and M4 evidence;
- LLVM and Cranelift bootstrap parity through the selected policy;
- Apple Developer ID signing identity and valid notarization profile;
- dual-native unsigned and signed universal execution;
- final digest-preserving promotion and rollback receipt.

## Final Verdict

**STATUS: FAIL / NOT COMPLETE.** Current source closes the latest worker-wire,
ABI-corpus, lint-catalog, enum-sealer, browser-degradation, temporary-storage,
memory, and progress-reporting slices. Multiple independent KPF product/source
gaps remain, and both plans still require unavailable native/release authority.
No native completion is inferred from structural or interpreter evidence.
