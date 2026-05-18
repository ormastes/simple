# SStack State: simple-smf-runtime-replacement

## User Request
> next task from the plan — simple_smf_runtime_replacement (shared header contract, hosted atomic replacement, interpreter/JIT integration, SimpleOS executable SMF, dynamic libraries)

## Task Type
feature

## Refined Goal
> Implement SMF runtime replacement models: shared header contract with trailer/offset-0 detection, hosted atomic generation states with candidate staging and symbol swap, JIT bridge with export/import metadata, and dynamic library loading with link namespaces.

## Acceptance Criteria
- [ ] AC-1: SmfHeader — magic bytes, version, section count, trailer offset, is_valid flag
- [ ] AC-2: TrailerDetection — detection mode (trailer/offset0/none), confidence, fallback used flag
- [ ] AC-3: HeaderFallback — primary mode, fallback mode, resolved header ref, detection order
- [ ] AC-4: GenerationState — state enum (loaded/candidate/active/retiring/failed), module name, generation id
- [ ] AC-5: CandidateMapping — candidate ref, relocation status, import validation pass/fail, ready to swap flag
- [ ] AC-6: SymbolSwap — old export ref, new export ref, swap status (pending/complete/rollback), drain count
- [ ] AC-7: SmfSource — source kind (file/jit/remote), module path, export count, import count
- [ ] AC-8: JitManifest — manifest id, candidate count, upload size, is_local flag
- [ ] AC-9: DynLoadRequest — library name, search path, load mode (lazy/eager), namespace ref
- [ ] AC-10: Verification spec — 20 tests covering headers, generations, JIT bridge, dynamic loading

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 5 plan phases. Existing: SMF reader/writer in compiler, moduleloader, kernel parser.

### 5-implement
<pending>

### 7-verify
<pending>
