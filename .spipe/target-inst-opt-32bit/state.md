# SStack State: target-inst-opt-32bit

## User Request
> impl and improve optimization plugin by plan - doc/01_research/local/target_instruction_optimization_32bit.md, doc/01_research/domain/target_instruction_optimization_32bit.md, doc/02_requirements/feature/target_instruction_optimization_32bit_options.md, doc/02_requirements/nfr/target_instruction_optimization_32bit_options.md, doc/04_architecture/target_instruction_optimization_32bit.md, doc/05_design/target_instruction_optimization_32bit.md, doc/03_plan/sys_test/target_instruction_optimization_32bit.md, doc/06_spec/app/compiler/feature/target_instruction_optimization_32bit_spec.spl, doc/03_plan/agent_tasks/target_instruction_optimization_32bit.md

## Task Type
feature

## Refined Goal
> Implement the target instruction optimization plugin (Option B: target matrix + x86-64 32-bit-form optimization) with NFR Option 2 (correctness + x86-64 non-regression), extending the existing MIR optimization pipeline and backend lowering to support per-target instruction families with legality/profitability gates, starting with x86-64 narrow-form selection and scaffolding for x86-32, AArch64, ARM32, RV64, and RV32.

## Acceptance Criteria
- [ ] AC-1: `TargetFamily` enum covers X86_64, X86_32, Aarch64, Arm32, Rv64, Rv32 with triple-parsing that correctly classifies each
- [ ] AC-2: `InstructionFamily` + `TargetEnableMatrix` correctly enables/disables families per target, returning `FamilyDecision` with reason and fallback
- [ ] AC-3: x86-64 32-bit-form legality prover accepts narrow u32/i32 values and rejects pointer truncation or unknown-width operands
- [ ] AC-4: Optimization planner flow (parse triple → build feature set → evaluate matrix → legality → profitability → dispatch) is wired into the existing `pipeline_optimize` path
- [ ] AC-5: Golden MIR/lowering tests pass for each enabled instruction family on x86-64, with at least unsupported-feature rejection tests for other targets
- [ ] AC-6: x86-64 optimized benchmark kernels produce same-or-smaller `.text` size and same-or-faster runtime vs baseline (within 3% noise)
- [ ] AC-7: All existing BDD spec tests in `target_instruction_optimization_32bit_spec.spl` pass

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-15
- [x] 2-research (Analyst) — 2026-05-15
- [x] 3-arch (Architect) — 2026-05-15
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: **feature**. Refined from 9 plan documents into Option B (target matrix + x86-64 32-bit-form optimization) with NFR Option 2 (correctness + non-regression gates). 7 acceptance criteria defined covering target family classification, enable matrix, legality proofs, planner integration, golden tests, benchmark gates, and BDD spec compliance. Scope: ~15-25 files across `60.mir_opt/`, `70.backend/`, and test fixtures.

### 2-research

#### Existing Infrastructure

**MIR Optimization Pipeline** (`src/compiler/60.mir_opt/mir_opt/mod.spl`):
- `OptimizationPipeline` struct with `passes: [MirPassDescriptor]`, `target_ctx: TargetOptContext`
- `TargetOptContext` struct: `x86_caps: X86Caps`, `cipher_remark: bool`, `caps_kind: TargetCapsKind`
- `pipeline_optimize(pipeline, module)` dispatches passes including `pattern_idiom`
- `optimize_module_with_caps(module, level, caps, cipher_remark)` — x86-only entry point
- `optimize_module_with_context(module, level, ctx)` — generic entry point (extension seam)
- Pass registry: dce, constant_folding, copy_prop, inline, cse, loop_licm, loop_opt, loop_strength, bounds_check_elim, outline, tco, gvn, pattern_idiom, auto_vectorize, predicate_promote

**Pattern Dispatch** (`src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl`):
- `run_pattern_idiom_pass`, `run_pattern_idiom_pass_x86`, `run_pattern_idiom_pass_generic`
- Rewrites `MirInstKind.Intrinsic` call sites gated on `TargetCapsKind` flags
- Uses `pattern/rule_engine.spl` (provider metadata, lookup stats) and `pattern/rules_crypto.spl` (cipher rules)

**Feature Caps** (`src/compiler/70.backend/feature_caps.spl`):
- `TargetIdiom` enum — cipher/SIMD operation tags
- `TargetCapsKind` enum: `X86(X86Caps) | Aarch64(Aarch64Caps) | Rv64(Rv64Caps) | None_`
- `caps_kind_from_triple(triple: text) -> TargetCapsKind` (line 766) — current triple parser
  - Handles `x86_64|x86-64`, `aarch64|armv8`, `rv64|riscv64`; everything else returns `None_`
  - **Gap**: No handling for `i686` (x86-32), `armv7`/`arm32`, `riscv32`
- Helper fns: `caps_kind_supports`, `caps_kind_cost`, `caps_kind_target_name`, `caps_kind_preferred_vector_width_bits`
- Per-target caps: `X86Caps`, `Aarch64Caps`, `Rv64Caps` with `supports(idiom)` and `cost(idiom)` methods

**Backend Lowering** (`src/compiler/70.backend/lowering/`):
- `intrinsic_lowering_x86.spl` (20KB) — exports `LoweringResult`, `intrinsic_to_target_idiom`, `lower_cipher_intrinsic_x86`
- `intrinsic_lowering_aarch64.spl` (16KB) — exports `intrinsic_to_target_idiom_aarch64`, `lower_cipher_intrinsic_aarch64`
- `intrinsic_lowering_riscv.spl` (15KB) — exports `intrinsic_to_target_idiom_riscv`, `lower_cipher_intrinsic_riscv`
- `__init__.spl` — re-exports all three

**Target Triple Prior Art**:
- `src/compiler/70.backend/backend/llvm_target.spl` — already handles `i686` (x86-32) and `armv7` arch strings in `LlvmTargetTriple`; closest pattern for triple parsing
- `src/compiler/80.driver/driver_types.spl` — has triple plumbing through driver
- `src/compiler/00.common/compiler_services.spl` — `target_triple_fn` callback surface (line 166, 222)

**Plugin Architecture** (`doc/04_architecture/simple_optimization_plugin.md`):
- `OptimizationProvider` with name, version, kind, target_filter, safety_class
- `RuleLookup` strategies: direct, prebuilt index, dynamic, whole-pass
- `rule_engine.spl` owns metadata; `rules_crypto.spl` owns built-in rules; `pattern_dispatch.spl` owns rewrite traversal
- LLVM backend optimization stays separate (uses LLVM `O*` pass pipelines)

**Compiler Opt Infra Refactor** (`doc/04_architecture/compiler_optimization_infra_refactor_2026-05-13.md`):
- Current boundary: rule_engine (metadata) / rules_crypto (definitions) / pattern_dispatch (rewrite + gating)

#### New Types Required (all confirmed non-existent via grep)

- `TargetFamily` enum: `X86_64, X86_32, Aarch64, Arm32, Rv64, Rv32`
- `TargetFeatureSet` struct: normalized CPU, ABI, feature flags, strictness, opt level
- `InstructionFamily` struct: stable id, target-family availability metadata
- `TargetEnableMatrix`: per-family enabled/disabled decisions
- `FamilyDecision` struct: enabled bool, disabled reason, source, fallback family
- `LegalityProof` struct: records why a rewrite is semantically safe

#### New Functions Required (spec API shape — free functions, not methods)

- `target_family_from_triple(triple: text) -> text` — AC-1
- `target_enable_matrix(triple: text, flags: [text]) -> TargetEnableMatrix` — AC-2
- `matrix_decision(matrix: TargetEnableMatrix, family_id: text) -> FamilyDecision` — AC-2
- `prove_x86_64_narrow_form(scenario: text) -> LegalityProof` — AC-3
- `compare_target_optimization_benchmark(target: text, kernel: text) -> BenchmarkResult` — AC-6

#### Architecture Choices for Phase 3

1. **TargetCapsKind vs TargetFamily**: `TargetCapsKind` has 4 variants (X86/Aarch64/Rv64/None_). Spec requires 6 families. Options: (a) extend `TargetCapsKind` with X86_32/Arm32/Rv32 variants, or (b) introduce `TargetFamily` as a separate higher-level enum and keep `TargetCapsKind` as cap-level detail. Decision for Phase 3.
2. **Entry point**: `optimize_module_with_caps` takes `X86Caps` directly — backward compat risk if changed. Safer to add `optimize_module_with_target(module, level, triple)` as new entry point.
3. **File placement**: new target-family/matrix code likely in `src/compiler/60.mir_opt/mir_opt/` (e.g., `target_family.spl`, `instruction_family.spl`). Legality prover in same directory. Lowering extensions in `src/compiler/70.backend/lowering/`.

#### Reusable Components

- `caps_kind_from_triple` — extend for new targets
- `pattern_dispatch` rewrite loop — add narrow-form dispatch key alongside `pattern_idiom`
- `LoweringResult` type from lowering module
- `InstructionCost` from `feature_caps.spl` for profitability scoring
- `OptimizationRuleProvider` from `rule_engine.spl` for provider registration
- LLVM target triple patterns from `llvm_target.spl` for triple normalization

#### Constraints

- **No inheritance** — composition, traits, mixins only
- **Generics use `<>` not `[]`**
- All code in `.spl` files
- Interpreter mode limitations (spec tests run interpreted; `it` block var mutation, named-arg calls have restrictions)
- Compile-mode false-greens: verify in interpreter mode
- `TargetCapsKind` match exhaustiveness — adding variants requires updating all match sites

#### Risks

- **Benchmark harness (AC-6)**: 3% noise gate needs fixture infrastructure that doesn't exist. Largest unknown for Phase 5.
- **Triple parser fragmentation**: `caps_kind_from_triple` and `llvm_target.spl` both parse triples independently. Adding a third parser (`target_family_from_triple`) risks divergence. Consider unifying or delegating.
- **TargetCapsKind match-site churn**: Adding 3 new variants (X86_32, Arm32, Rv32) touches every `match kind:` in `feature_caps.spl` and `pattern_dispatch.spl`.
- **Spec API contract**: Spec expects free functions returning text/structs — implementation must match this exact surface, not OO methods.
- **`caps_kind_from_triple` returns `None_` for i686/riscv32/arm32**: AC-1 spec will fail until this or a parallel function is extended.

#### 6-Task Work Breakdown (from `doc/03_plan/agent_tasks/target_instruction_optimization_32bit.md`)

1. **Task 1 — Target matrix owner**: `TargetFamily`, `InstructionFamily`, `TargetEnableMatrix`, `FamilyDecision` types + triple parsing
2. **Task 2 — Optimization planner owner**: shared family registry, cached planner, provider filtering by target
3. **Task 3 — x86-64 narrow-form owner**: legality checks, golden tests, benchmark fixtures
4. **Task 4 — Native IA-32 owner**: x86-32 backend scaffolding (future milestone)
5. **Task 5 — ARM/RISC-V family owner**: conservative feature tables, lowering hooks, fallback tests
6. **Task 6 — Benchmark owner**: perf harness, baseline/optimized comparison, 3% noise gate

#### Key File Paths

- `src/compiler/60.mir_opt/mir_opt/mod.spl` — pipeline + TargetOptContext
- `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` — idiom dispatch
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` — provider metadata
- `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` — cipher rules
- `src/compiler/60.mir_opt/mir_opt/pattern/cost_model.spl` — cost model
- `src/compiler/70.backend/feature_caps.spl` — TargetIdiom, TargetCapsKind, caps
- `src/compiler/70.backend/lowering/__init__.spl` — lowering re-exports
- `src/compiler/70.backend/lowering/intrinsic_lowering_x86.spl` — x86 lowering
- `src/compiler/70.backend/lowering/intrinsic_lowering_aarch64.spl` — AArch64 lowering
- `src/compiler/70.backend/lowering/intrinsic_lowering_riscv.spl` — RISC-V lowering
- `src/compiler/70.backend/backend/llvm_target.spl` — triple parsing prior art
- `src/compiler/80.driver/driver_types.spl` — driver triple plumbing
- `src/compiler/00.common/compiler_services.spl` — target_triple_fn callback
- `doc/06_spec/app/compiler/feature/target_instruction_optimization_32bit_spec.spl` — BDD spec

### 3-arch

**Decision: TargetFamily is a parallel enum, not an extension of TargetCapsKind.**
TargetCapsKind carries heavyweight capability payloads (X86Caps, etc.); adding 3 new variants requires stub cap structs and touches every existing match site. TargetFamily is a cheap classification enum with zero existing consumers. TargetCapsKind stays unchanged for backward compat.

**Decision: Canonical triple parser lives in target_family.spl.**
`caps_kind_from_triple` and `llvm_target.spl` stay as-is. `target_family.spl` is the single canonical parser for family classification; other parsers may delegate to it later (out of scope).

**Decision: New entry point, don't touch existing ones.**
Add `optimize_module_with_target(module, level, triple, flags)` that builds `TargetOptContext` internally and calls `optimize_module_with_context`. `optimize_module_with_caps` is untouched.

**Decision: All new public functions use positional args only.**
Interpreter mode rejects named-arg calls. Struct construction via `_new` factory functions, not field-named literals at spec call sites.

#### New Files

| File | Layer | Exports |
|------|-------|---------|
| `src/compiler/60.mir_opt/mir_opt/target_family.spl` | L1 Identity | `TargetFamily` enum, `TargetFeatureSet` struct, `target_family_from_triple(text) -> text`, `target_family_enum_from_triple(text) -> TargetFamily`, `target_family_name(TargetFamily) -> text`, `target_feature_set_new(text, [text]) -> TargetFeatureSet` |
| `src/compiler/60.mir_opt/mir_opt/instruction_family.spl` | L2 Matrix | `InstructionFamily` struct, `FamilyDecision` struct, `TargetEnableMatrix` struct, `target_enable_matrix(text, [text]) -> TargetEnableMatrix`, `matrix_decision(TargetEnableMatrix, text) -> FamilyDecision`, `instruction_family_new(text, text, [text], [text], text, i64, text) -> InstructionFamily` |
| `src/compiler/60.mir_opt/mir_opt/narrow_form_legality.spl` | L3 Legality | `LegalityProof` struct, `prove_x86_64_narrow_form(text) -> LegalityProof`, `legality_proof_new(text, text, text) -> LegalityProof` |
| `src/compiler/60.mir_opt/mir_opt/target_profitability.spl` | L4 Profitability | `profitability_score(TargetEnableMatrix, text, InstructionCost) -> i64`, `should_rewrite(i64) -> bool` — extends `cost_model.spl` (37-line scaffold) with target-aware scoring |
| `src/compiler/60.mir_opt/mir_opt/target_opt_planner.spl` | L5 Planner | `optimize_module_with_target(MirModule, OptLevel, text, [text]) -> MirModule`, `plan_target_optimizations(TargetFeatureSet, TargetEnableMatrix) -> [text]` |
| `src/compiler/60.mir_opt/mir_opt/target_benchmark.spl` | Benchmark | `BenchmarkResult` struct, `compare_target_optimization_benchmark(text, text) -> BenchmarkResult` |

#### Modified Files

| File | Change |
|------|--------|
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | Add `optimize_module_with_target` import; register `target_narrow_form` pass in `mir_pass_descriptor_registry`; add dispatch case in `run_pass_on_module` |
| `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` | Add `run_narrow_form_pass(MirModule, TargetEnableMatrix, TargetFeatureSet) -> MirModule` alongside existing `run_pattern_idiom_pass_generic` |
| `src/compiler/60.mir_opt/mir_opt/pattern/cost_model.spl` | Extend scaffold (37 lines) with `target_profitability_cost(InstructionCost, InstructionCost) -> i64` for narrow-vs-wide comparison |
| `src/compiler/70.backend/feature_caps.spl` | Add `caps_kind_for_family(TargetFamily) -> TargetCapsKind` bridge function (no enum variant changes) |

#### Key Interfaces (positional args, no inheritance)

```
# L1 — target_family.spl
fn target_family_from_triple(triple: text) -> text
fn target_family_enum_from_triple(triple: text) -> TargetFamily
fn target_feature_set_new(triple: text, flags: [text]) -> TargetFeatureSet

# L2 — instruction_family.spl
fn target_enable_matrix(triple: text, flags: [text]) -> TargetEnableMatrix
fn matrix_decision(matrix: TargetEnableMatrix, family_id: text) -> FamilyDecision

# L3 — narrow_form_legality.spl
fn prove_x86_64_narrow_form(scenario: text) -> LegalityProof

# L4 — target_profitability.spl
fn profitability_score(matrix: TargetEnableMatrix, family_id: text, cost: InstructionCost) -> i64

# L5 — target_opt_planner.spl
fn optimize_module_with_target(module: MirModule, level: OptLevel, triple: text, flags: [text]) -> MirModule

# Benchmark — target_benchmark.spl
fn compare_target_optimization_benchmark(target: text, kernel: text) -> BenchmarkResult
```

#### Data Flow

```
triple text ──→ target_family_enum_from_triple ──→ TargetFamily
                         │
          ┌──────────────┘
          ▼
target_feature_set_new(triple, flags) ──→ TargetFeatureSet
          │
          ▼
target_enable_matrix(triple, flags) ──→ TargetEnableMatrix
          │                                     │
          │              matrix_decision(matrix, family_id)
          │                                     │
          │                                     ▼
          │                              FamilyDecision
          │                              (enabled / reason / fallback)
          │
          ▼
plan_target_optimizations ──→ [family_id]
          │
          ├──→ prove_x86_64_narrow_form ──→ LegalityProof (accept/reject)
          │
          ├──→ profitability_score ──→ i64 (>0 = profitable)
          │
          └──→ dispatch via run_narrow_form_pass in pattern_dispatch
```

#### Integration Strategy

1. `optimize_module_with_target` is a **new entry point** — existing `optimize_module_with_context` and `optimize_module_with_caps` are untouched. Callers adopt the new function when ready.
2. `target_narrow_form` is registered as a new pass in `mir_pass_descriptor_registry` (like `pattern_idiom`). It is only added to pipeline levels `Speed` and `Aggressive`.
3. `run_narrow_form_pass` in `pattern_dispatch.spl` follows the same per-function loop pattern as `run_pattern_idiom_pass_generic`. It queries `TargetEnableMatrix` before touching any instruction.
4. `caps_kind_for_family` in `feature_caps.spl` bridges TargetFamily→TargetCapsKind so narrow-form dispatch can reuse existing `InstructionCost` queries without duplicating tables.
5. Benchmark harness (AC-6) is a thin interface contract — `BenchmarkResult` struct + `compare_target_optimization_benchmark`. Full fixture infrastructure is a Phase 5 risk; design provides the API surface only.

#### Phase 4/5 Notes

- **Pass ordering**: `target_narrow_form` runs **before** `pattern_idiom`. Narrow-form prover needs original bit-width info; pattern_idiom rewrites sequences into intrinsics that obscure widths.
- **`caps_kind_for_family` for 32-bit families**: Returns `TargetCapsKind.None_` for X86_32/Arm32/Rv32 until cap structs exist. Phase 5 must handle `None_` gracefully in profitability queries.
- **Unknown triple default**: `target_family_from_triple("garbage")` returns `"Unknown"`. Internal enum: `TargetFamily.Unknown`.
- **BenchmarkResult fields**: Must include `baseline_runs: i64` and `optimized_runs: i64` to match BDD spec reads.

#### Risks Carried to Phase 5

- Benchmark fixture infra (AC-6): 3% noise gate needs baseline/optimized MIR compilation + timing harness. Largest implementation unknown.
- `cost_model.spl` scaffold (37 lines): needs real profitability logic; current file is header-only.

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
