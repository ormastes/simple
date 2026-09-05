# SStack State: general-mir-bulk-ops

## User Request
> Add general MIR bulk byte copy/fill/compare recognizer passes emitting bulk_copy_hint, bulk_fill_hint, bulk_cmp_hint intrinsics (sibling to existing bulk_store_hint in optimization_passes.spl). Also add endian load/store swap recognizer emitting endian_load_hint/endian_store_hint. Relabel "FS IO Optimization Passes" section to "General IO Optimization Passes" since they match MIR shapes not FS identifiers. Add CLibParityHotspot provider entries for the new transforms. Spec covers both generic loop cases AND FS-shaped test cases to prove generality. No benchmark refresh, no default flips, no QEMU.

## Task Type
feature

## Refined Goal
> Add five new general-purpose MIR optimization recognizer passes to the existing optimization pipeline in `src/compiler/60.mir_opt/optimization_passes.spl`:
> 1. **bulk_copy_hint** — recognize Load+Store loops copying contiguous memory regions
> 2. **bulk_fill_hint** — recognize Store loops writing repeated constant values to contiguous memory
> 3. **bulk_cmp_hint** — recognize Load+Load+Compare loops comparing two contiguous memory regions
> 4. **endian_load_hint** — recognize byte-shift-OR patterns assembling multi-byte values (little/big endian decode)
> 5. **endian_store_hint** — recognize shift-AND-Store patterns splitting multi-byte values into bytes (endian encode)
>
> These are general MIR-shape transforms, not filesystem-specific. They emit intrinsic hints that backends can lower to memcpy/memset/memcmp/bswap or leave as-is.
>
> Additionally: relabel the existing "FS IO Optimization Passes" section header to "General IO Optimization Passes", register CLibParityHotspot provider entries for the new transforms in the rule engine, and write specs that prove generality (generic + FS-shaped test cases).

## Acceptance Criteria
- [ ] AC-1: `optimize_bulk_copy` recognizes Load→Store loops on contiguous GEP offsets and emits `bulk_copy_hint` intrinsic
- [ ] AC-2: `optimize_bulk_fill` recognizes Store loops with constant value on contiguous GEP offsets and emits `bulk_fill_hint` intrinsic
- [ ] AC-3: `optimize_bulk_cmp` recognizes Load+Load+Compare loops on two contiguous GEP bases and emits `bulk_cmp_hint` intrinsic
- [ ] AC-4: `optimize_endian_load` recognizes byte-shift-OR patterns and emits `endian_load_hint` intrinsic with byte-order metadata
- [ ] AC-5: `optimize_endian_store` recognizes shift-AND-Store patterns and emits `endian_store_hint` intrinsic with byte-order metadata
- [ ] AC-6: "FS IO Optimization Passes" section header renamed to "General IO Optimization Passes" in optimization_passes.spl
- [ ] AC-7: CLibParityHotspot provider entries registered in rule_engine.spl for each new transform
- [ ] AC-8: Spec file covers generic loop cases (plain array copy/fill/cmp) AND FS-shaped cases (directory entry copy, sector buffer compare) to prove transforms are not FS-specific
- [ ] AC-9: All existing optimization_passes tests still pass (no regression)
- [ ] AC-10: Count functions (`count_bulk_copy`, `count_bulk_fill`, `count_bulk_cmp`, `count_endian_load`, `count_endian_store`) exist for statistics reporting

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-26
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: feature. Refined user request into 5 new general MIR recognizer passes + relabeling + CLibParityHotspot registration + generality-proving specs. 10 acceptance criteria defined. Key files: `src/compiler/60.mir_opt/optimization_passes.spl` (main impl), `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` (provider registration), new spec file.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
