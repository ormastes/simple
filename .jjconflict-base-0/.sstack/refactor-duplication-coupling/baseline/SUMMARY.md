# Duplication Baseline — line/token mode

Generated: 2026-04-27
Tool: bin/simple duplicate-check
Args: --min-lines 5 --min-impact 50 --format text
Scope: src/compiler/ (per-layer, parallel)

## Per-layer totals

| Layer | Files | Groups | Dup lines |
|-------|-------|--------|-----------|
| 00.common | 39 | 0 | 0 |
| 10.frontend | 106 | 15 | 308 |
| 15.blocks | 26 | 0 | 0 |
| 20.hir | 19 | 0 | 0 |
| 25.traits | 9 | 0 | 0 |
| 30.types | 57 | 6 | 146 |
| 35.semantics | 60 | 21 | 691 |
| 40.mono | 22 | 7 | 163 |
| 50.mir | 19 | 2 | 48 |
| 55.borrow | 10 | 0 | 0 |
| 60.mir_opt | 27 | 2 | 48 |
| 70.backend | 205 | 38 | 919 |
| 80.driver | 98 | 17 | 375 |
| 85.mdsoc | 146 | 0 | 0 |
| 90.tools | 186 | 18 | 491 |
| 95.interp | 14 | 0 | 0 |
| 99.loader | 27 | 1 | 24 |
| **TOTAL** | — | **127** | **3213** |

## Top 20 hotspot groups across all layers

- **impact 800** [35.semantics] 10x8 lines  first: `src/compiler/35.semantics/lint/mcp_perf_lint.spl:106-113`
- **impact 700** [35.semantics] 10x7 lines  first: `src/compiler/35.semantics/lint/mcp_perf_lint.spl:105-111`
- **impact 648** [35.semantics] 9x8 lines  first: `src/compiler/35.semantics/lint/mcp_perf_lint.spl:107-114`
- **impact 512** [35.semantics] 8x8 lines  first: `src/compiler/35.semantics/lint/mcp_perf_lint.spl:110-117`
- **impact 320** [80.driver] 8x5 lines  first: `src/compiler/80.driver/shb/shb_reader.spl:100-104`
- **impact 320** [70.backend] 8x5 lines  first: `src/compiler/70.backend/backend/vhdl_backend.spl:2284-2288`
- **impact 288** [35.semantics] 6x8 lines  first: `src/compiler/35.semantics/lint/remote_exec_lint.spl:52-59`
- **impact 245** [70.backend] 7x5 lines  first: `src/compiler/70.backend/backend/native/x86_64_simd.spl:158-162`
- **impact 216** [70.backend] 6x6 lines  first: `src/compiler/70.backend/backend/cranelift_type_mapper.spl:129-134`
- **impact 216** [70.backend] 6x6 lines  first: `src/compiler/70.backend/backend/common/type_mapper.spl:196-201`
- **impact 180** [70.backend] 6x5 lines  first: `src/compiler/70.backend/backend/cranelift_type_mapper.spl:131-135`
- **impact 180** [70.backend] 6x5 lines  first: `src/compiler/70.backend/backend/cranelift_type_mapper.spl:130-134`
- **impact 175** [90.tools] 5x7 lines  first: `src/compiler/90.tools/fix/main.spl:248-254`
- **impact 150** [90.tools] 5x6 lines  first: `src/compiler/90.tools/fix/main.spl:247-252`
- **impact 128** [70.backend] 4x8 lines  first: `src/compiler/70.backend/backend/native/isel_aarch64.spl:121-128`
- **impact 128** [70.backend] 4x8 lines  first: `src/compiler/70.backend/backend/c_codegen_adapter.spl:25-32`
- **impact 128** [30.types] 4x8 lines  first: `src/compiler/30.types/type_layout.spl:197-204`
- **impact 128** [30.types] 4x8 lines  first: `src/compiler/30.types/type_layout.spl:196-203`
- **impact 125** [90.tools] 5x5 lines  first: `src/compiler/90.tools/header_gen/c_header.spl:178-182`
- **impact 125** [70.backend] 5x5 lines  first: `src/compiler/70.backend/backend/native/arm_neon.spl:93-97`

---

## Cosine-mode baseline (added 2026-04-27)

Generated via sequential per-layer runs (parallel runs starve the interpreter).
Cosine catches structural similarity beyond exact-text duplication.

| Layer | Groups | Dup lines | Δ vs line |
|-------|-------:|----------:|----------:|
| 10.frontend | 19 | 450 | +4 / +142 |
| 30.types | 6 | 146 | 0 |
| 35.semantics | 21 | 691 | 0 |
| 40.mono | 7 | 163 | 0 |
| 50.mir | 2 | 48 | 0 |
| 60.mir_opt | 2 | 48 | 0 |
| 70.backend | 38 | 919 | 0 |
| 80.driver | 17 | 375 | 0 |
| 85.mdsoc | 0 | 0 | 0 |
| 90.tools | 19 | 509 | +1 / +18 |
| 99.loader | 2 | 62 | +1 / +38 |
| **TOTAL** | **133** | **3,411** | **+6 / +198** |

**New cosine-only findings worth attention:**
- `10.frontend/core/ast.spl` impact **312** (6×8 lines) — NEW hotspot not surfaced by line-mode. Add to ARCHITECTURE.md as additional batch.
- 4 other minor 10.frontend additions (impact <150).
- 1 new in 90.tools, 1 new in 99.loader.

**Conclusion:** ARCHITECTURE.md's 18-batch plan stands. Add an additional batch (1.5 or insert at appropriate position) for `10.frontend/core/ast.spl`. The other 5 additions are small enough to absorb into existing same-layer batches (16, 17, 18).
