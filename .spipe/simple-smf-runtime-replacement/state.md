# SStack State: simple-smf-runtime-replacement

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — simple_smf_runtime_replacement (shared header contract, hosted atomic replacement, interpreter/JIT integration, SimpleOS executable SMF, dynamic libraries)

## Task Type
feature

## Refined Goal
> Implement SMF runtime replacement models: shared header contract with trailer/offset-0 detection, hosted atomic generation states with candidate staging and symbol swap, JIT bridge with export/import metadata, and dynamic library loading with link namespaces.

## Acceptance Criteria
- [x] AC-1: SmfHeader — magic bytes, version, section count, trailer offset, is_valid flag
- [x] AC-2: TrailerDetection — detection mode (trailer/offset0/none), confidence, fallback used flag
- [x] AC-3: HeaderFallback — primary mode, fallback mode, resolved header ref, detection order
- [x] AC-4: GenerationState — state enum (loaded/candidate/active/retiring/failed), module name, generation id
- [x] AC-5: CandidateMapping — candidate ref, relocation status, import validation pass/fail, ready to swap flag
- [x] AC-6: SymbolSwap — old export ref, new export ref, swap status (pending/complete/rollback), drain count
- [x] AC-7: SmfSource — source kind (file/jit/remote), module path, export count, import count
- [x] AC-8: JitManifest — manifest id, candidate count, upload size, is_local flag
- [x] AC-9: DynLoadRequest — library name, search path, load mode (lazy/eager), namespace ref
- [x] AC-10: Verification spec — 20 tests covering headers, generations, JIT bridge, dynamic loading

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 5 plan phases. Existing: SMF reader/writer in compiler, moduleloader, kernel parser.

### 5-implement
4 source + 1 test:
- src/os/smf/smf_header_contract.spl — SmfHeader + TrailerDetection + HeaderFallback + SmfTestVector
- src/os/smf/smf_generation.spl — GenerationState + CandidateMapping + SymbolSwap + RetiredMapping
- src/os/smf/smf_jit_bridge.spl — SmfSource + ExportMetadata + ImportMetadata + JitManifest
- src/os/smf/smf_dynlib.spl — LibraryRole + LinkNamespace + DynLoadRequest + DynLoadResult
- test/unit/os/smf_runtime_spec.spl — 20 tests

### 7-verify
20/20 tests PASS. Fixed: reserved keyword gen->g, ref->r; to_equal(false) workaround (bug SPEC-TOEQUAL-FALSE filed).
