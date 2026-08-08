# Optimizer Infrastructure Research — Workstream B

Date: 2026-05-25  
Scope: AC-6 (perf-compare harness), AC-7 (rule engine .opt.json), AC-8 (C-parity MIR passes), AC-9 (CLI surface)

---

## 1. Existing MIR Pass Infrastructure

### Pass Registry (`src/compiler/60.mir_opt/mir_opt/mod.spl`)

`PassKind` enum and `MirPassDescriptor` registry are fully defined. All 25+ passes are registered via `mir_pass_descriptor_registry()`:

```
DeadCodeElimination, ConstantFolding, CopyPropagation, CommonSubexprElim,
InlineSmallFunctions, InlineFunctions, InlineAggressive,
LoopInvariantMotion, LoopUnroll, BoundsCheckElimination,
StrengthReduction, CollectionOpt, StringBuilderOpt, BodyOutlining,
GeneratorStateMachine, TailCallOptimization, GlobalValueNumbering,
PatternIdiom, AutoVectorize, PredicatePromote, TargetNarrowForm,
WriteCoalesce, ReadAheadHoist, SyscallBatch, TypedByteCanon
```

Key: `PassScope` is `Function | Module | FsDriver`. Pass dispatch runs `run_pass_on_module` which matches `PassKind` then falls through to `DynamicPassRegistry`.

**Status for AC-8**: `BoundsCheckElimination`, `LoopInvariantMotion`, `CopyPropagation` (copy→move promotion) are **already registered as PassKind variants** in the registry. The implementations are pipeline stubs (`mir_pipeline_provider(..., false)`) — the pass names exist but the transform bodies need to be written.

### Pass Execution (`optimization_passes.spl`)

Actual pass bodies exist for:
- `ConstantFolding` — constant folding/propagation, strength reduction (x*2→x<<1), algebraic simplifications, dead code elimination, peephole
- `WriteCoalesce` — batches consecutive GEP+Store to same base
- `ReadAheadHoist` — loop-invariant Load/Call hoisting (detection + counting done, `optimize_read_ahead_hoist` moves them)
- `SyscallBatch` — consecutive calls to same function ID counted for batching

**Missing implementation bodies**: `BoundsCheckElimination`, `CopyPropagation` (copy→move), the loop-invariant *motion* (hoisting already exists via `ReadAheadHoist`) — these need to wire `PassKind.LoopInvariantMotion` → actual LICM pass.

---

## 2. Rule Engine (`src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`)

Key types:
```
struct Rule { name, intrinsic, requires, cost_delta, software_cost }
struct MatchHit { rule_name, intrinsic, call_site }
struct OptimizationRuleProvider { name, version, kind: OptimizerProviderKind, load_mode, lookup_kind, path, hot_path, enabled, required_facts, produced_facts, safety_class }
enum OptimizerProviderKind { Syntax|Hir|Mir|Pattern|Interpreter|JitHotspot|BackendMetadata|CLibParityHotspot }
enum OptimizerRuleLookupKind { DirectExact|IndexedExact|DynamicExact|PipelinePass }
```

Factory functions: `optimization_rule_provider_builtin_with_contract(name, kind, lookup_kind, hot_path, required_facts, produced_facts, safety_class)`.

**For AC-7 (.opt.json rule files)**: The `DynamicPassRegistry` system in `optimizer_manifest.spl` loads `.sdn/.json` manifests with schema:
```json
{ "schema_version": 1, "compiler_abi": "simple.opt.mir.v1", "name": "...", "version": "...",
  "min_compiler_version": "...", "passes": [...] }
```
Per-pass fields: `stable_name`, `aliases`, `scope`, `capability_requires`, `required_facts`, `produced_facts`, `safety_class`.  
Load path: `load_manifest_v1(json)` → `OptimizerManifest` → `dynamic_pass_registry_register(registry, manifest)`.

**Gap**: Rule files are `.sdn/.json`, not `.opt.json`. The `.opt.json` extension for AC-7 would be an alias or new convention. The load/validate infra is a skeleton — `load_manifest_v1_from_parsed` exists but the actual dynamic dispatch in `run_pass_on_module` after `DynamicPassRegistry` lookup needs wiring.

### CLib Parity Rules (`rules_clib_parity.spl`)

10 rules in 3 families (ByteCopy: memcpy/memmove/memset, EndianLoad: le16/le32/be32/be64, ChecksumReducer: checksum_fold/crc32/adler32). Pattern kind + intrinsic + cost_delta. Provider uses `OptimizerProviderKind.CLibParityHotspot`.

---

## 3. C Backend Path (AC-6 — C codegen comparison)

### C Backend exists and is real:
- `src/compiler/70.backend/backend/c_backend.spl` — `CCodegenBackend` implementing Codegen trait
- `src/compiler/70.backend/backend/c_codegen_adapter.spl` — `CCodegenAdapter` wrapping `MirToC`
- `src/compiler/70.backend/backend/c_backend_translate.spl` — `MirToC` class, `translate_module(module: MirModule) -> text`
- Split translation: `c_backend_translate_part1/2/3.spl`, `c_backend_translate_ops.spl`

Output is **C++20** suitable for `clang++ -std=c++20 -O2 generated.cpp runtime.c -o output`.

The `CCodegenBackend` has `output_kind() = CodegenOutputKind.TextSource` — it emits `.cpp` text, not a compiled binary. There is **no built-in "compile the C and run it" path** in the backend itself.

**For AC-6 (compare harness)**: Need to:
1. Call `CCodegenAdapter.compile_module(module)` to get C++ source text
2. Write to temp file
3. `shell_output("clang++ -std=c++20 -O2 ...")` to compile
4. Time both the Simple-codegen binary and C++-codegen binary

`shell_output` is already available (`use std.io_runtime.{shell_output}`). The linker wrapper already invokes `cc` as fallback — same pattern applies here.

---

## 4. MIR Representation (AC-8 pattern matching)

Source: `src/compiler/50.mir/mir_instructions.spl`

Key types:
```
struct MirBlock { id: BlockId, instructions: [MirInst], terminator: MirTerminator }
struct MirInst { kind: MirInstKind, ... }
enum MirInstKind { Const(dest, ...), Copy(dest, src), Move(dest, src), BinOp(dest, op, l, r),
  UnaryOp(dest, op, src), Cast(dest, ty, src), Load(dest, ptr), Store(ptr, val),
  Alloc(dest, ty), GetElementPtr(dest, base, indices), GetField(dest, base, idx),
  Aggregate(dest, kind, operands), Call(dest?, func, args), ... }
struct MirOperand { kind: MirOperandKind }
enum MirOperandKind { Copy(LocalId) | Move(LocalId) | ConstInt(i64) | ConstFloat(f64) | ConstBool(bool) }
struct MirFunction { blocks: [MirBlock], locals: [...], ... }
enum MirTerminator { Goto(BlockId) | If(cond, then_: BlockId, else_: BlockId) | Return(...) | ... }
```

Pattern matching on `inst.kind` with `match ... case Const(...) | Copy(...) | BinOp(...)` is the existing idiom used throughout `optimization_passes.spl`.

**For AC-8 bounds-check elision**: Look for `BoundsCheck(dest, idx, len)` or equivalent instruction kind — the pass name exists but the MirInstKind variant needs verification (not found by name in the grep; may be represented as a `Call` to a bounds-check intrinsic or as a guard pattern).

---

## 5. CLI Surface (AC-9 — `bin/simple optimize`)

### Current state:
- No `optimize` subcommand in CLI dispatch (`src/app/cli/main_part1.spl`, `main_part2.spl`)
- `src/app/perf/` directory exists with `optimizer.smf`, `profiler.smf`, `benchmark.smf`, `render_adapter.spl` — but these are compiled `.smf` binaries, not source entry points visible in CLI
- `src/compiler/90.tools/perf/optimizer.spl` is a text-analysis-based optimizer (finds patterns in source text, not MIR), reports suggestions via `OptSuggestion` list; has `analyze_project()` + `generate_report()`
- CLI routing is in `src/app/cli/main_part1.spl` and `main_part2.spl`; subcommands map to `src/app/<name>/` directories

### What's needed for AC-9:
- New subcommand `optimize` → `src/app/optimize/` with `main.spl`
- Wire into CLI dispatch (match `"optimize"` in main_part1 or main_part2)
- Or extend the `perf` subcommand: `src/app/perf/` already exists

The `src/app/cli/main_cli_migration.spl` struct has flags like `interpret_optimized: bool`, `interpreter_mode: text` — shows how CLI args feed into execution paths.

---

## 6. Key Gaps Summary

| AC | Status | Gap |
|----|--------|-----|
| AC-6 (compare harness) | Infrastructure exists | No "compile C++ + time both" orchestrator; `shell_output` + `CCodegenAdapter` available |
| AC-7 (rule engine .opt.json) | Schema + load infra skeleton | Dynamic dispatch in `run_pass_on_module` after manifest lookup not wired; extension `.opt.json` vs `.sdn/.json` |
| AC-8 (C-parity passes) | PassKind variants registered | `BoundsCheckElimination` and `CopyPropagation` bodies missing; `LoopInvariantMotion` may alias `ReadAheadHoist`; `BoundsCheck` MirInstKind variant needs verification |
| AC-9 (CLI) | No `optimize` subcommand | Need entry in `src/app/optimize/main.spl` + CLI dispatch wiring |

---

## 7. Reuse Anchors

| Concern | File | Key symbol |
|---------|------|------------|
| Pass registration | `src/compiler/60.mir_opt/mir_opt/mod.spl` | `mir_pass_descriptor_registry()`, `run_pass_on_module()` |
| Pass bodies | `src/compiler/60.mir_opt/optimization_passes.spl` | `optimize_read_ahead_hoist`, `optimize_write_coalesce` |
| Rule engine types | `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` | `OptimizationRuleProvider`, `Rule`, `MatchHit` |
| CLib parity rules | `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl` | `clib_parity_rule_table()`, `CLibParityRule` |
| Manifest load/validate | `src/compiler/60.mir_opt/optimizer_manifest.spl` | `load_manifest_v1()`, `DynamicPassRegistry` |
| C backend | `src/compiler/70.backend/backend/c_codegen_adapter.spl` | `CCodegenAdapter.compile_module()` → C++ text |
| C translate | `src/compiler/70.backend/backend/c_backend_translate.spl` | `MirToC.translate_module()` |
| MIR types | `src/compiler/50.mir/mir_instructions.spl` | `MirInstKind`, `MirBlock`, `MirFunction`, `MirOperand` |
| Shell invoke | `std.io_runtime` | `shell_output(cmd)`, `process_run(...)` |
| CLI dispatch | `src/app/cli/main_part1.spl` | subcommand match block |
| Existing perf tool | `src/compiler/90.tools/perf/optimizer.spl` | `analyze_project()`, `OptSuggestion` |
