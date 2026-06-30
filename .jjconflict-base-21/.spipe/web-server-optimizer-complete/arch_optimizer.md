# Optimizer Architecture — web-server-optimizer-complete (AC-6 through AC-9)

Phase 3 architecture document. Covers all four acceptance criteria.
Verified against source on 2026-05-25.

---

## Verified facts (pre-write verification)

| Question | Answer |
|---|---|
| `BoundsCheck` in `MirInstKind`? | **No.** Enum has no `BoundsCheck` variant. Lowering confirmed in `mir_lowering_expr_part1.spl:43` — emits `MirInstKind.Intrinsic(nil, "bounds_check", [idx_op, len_op])`. Pass recognises `is_bounds_check_intrinsic(name)` helper (already in `bounds_check_elim.spl:166`) which matches `"bounds_check"`, `"array_bounds_check"`, `"rt_bounds_check"`, `"__simple_bounds_check"`. |
| `src/app/optimize/` exists? | **No.** New directory. `src/app/` has a flat list of sub-apps; `optimize/` must be created. |
| `OptSuggestion` type? | `class OptSuggestion` in `src/compiler/90.tools/perf/optimizer.spl` with fields `severity:text, file:text, line:i64, message:text, suggestion:text`. Reuse exactly. |
| Match arms for stub passes? | `run_pass_on_module` already has `case CopyPropagation:`, `case LoopInvariantMotion:`, `case BoundsCheckElimination:` at lines 637/654/662 — all no-ops. Wire bodies there. |
| `optimize_read_ahead_hoist` status? | Full body exists in `optimization_passes.spl`. Moves loop-invariant `Load` and `Call` instructions above loop header. `LoopInvariantMotion` delegates to it + adds generic BinOp hoisting. |
| `.opt.json` vs existing ABI? | Existing ABI is `simple.opt.mir.v1` with per-pass metadata. AC-7 extends v1 schema with an optional `rules: [PatternRule]` array — single ABI, single loader. |

---

## Resolved design decisions

**D1 — `.opt.json` ABI**: Extend `simple.opt.mir.v1` manifest schema with an optional `rules` array. Files with `.opt.json` extension are loaded identically to `.json` manifests. No new ABI string needed. A manifest may have zero passes but non-zero rules, or both.

**D2 — Dynamic pass execution model**: There is no plugin dlopen. A dynamically loaded rule file feeds a single built-in `PatternRulePass`. `run_pass_on_module` dispatches `PassKind.PatternIdiom` → `PatternRulePass.run(module, loaded_rules)`. The `DynamicPassRegistry` holds rule tables, not code.

**D3 — `MirPattern` JSON representation**: Single-instruction peephole scope. Wildcards use `"$name"` string prefix. **Binding semantics**: first occurrence of a wildcard name binds the concrete value; subsequent occurrences in the same slot array enforce equality (e.g. `dest: "$x"` and `operand_0: "$x"` both being `$x` means they must resolve to the same local). Sequence matching (N instructions) is out of scope for this phase. See AC-7 example rules below.

**D4 — AC-6 comparison**: Compares unoptimized-MIR-path vs optimized-MIR-path, both compiled through C++ (clang++). Optional `--native` flag adds Cranelift path as a third leg. This isolates MIR-pass value cleanly.

**D5 — `--apply` semantics**: Writes optimized MIR to a `.mir.json` sidecar next to the source file. Does not modify the `.spl` source. Prints a diff summary.

**D6 — LICM vs ReadAheadHoist**: `PassKind.LoopInvariantMotion` is the general pass. Its body calls `optimize_read_ahead_hoist` (existing, handles Load/Call) plus adds generic `BinOp` and `Copy` hoisting. `ReadAheadHoist` stays as a standalone fast-path that only handles Load/Call.

---

## AC-6 — Perf-Comparison Harness

### File: `src/app/optimize/compare.spl`

```
use std.io_runtime.{shell_output, write_file, temp_dir}
use compiler.mir_opt.mir_opt.mod.{run_typed_pass_on_module, OptLevel}
use compiler.backend.c.c_codegen_adapter.{CCodegenAdapter}
use compiler.mir.{MirModule}
```

#### Key types

```
struct BenchResult:
    label:        text         # "unoptimized" | "optimized" | "native"
    wall_ms:      i64
    instructions: i64?         # from perf stat, nil if perf not available
    binary_path:  text

struct CompareReport:
    source_file:  text
    results:      [BenchResult]
    regression:   bool          # true if optimized wall_ms > unoptimized * 1.05
    speedup_pct:  i64           # (unopt - opt) / unopt * 100

struct CompareConfig:
    passes:       [text]        # pass names to apply; empty = default pipeline
    level:        OptimizationLevel  # existing enum: None_/Basic/Standard/Aggressive
    runs:         i64           # warmup+measure repetitions, default 5
    use_perf:     bool          # try perf stat for instruction counts
    native_leg:   bool          # add Cranelift path as third leg

# CLI flag --level=O0|O1|O2|O3 maps to existing OptimizationLevel:
#   O0 → OptimizationLevel.None_
#   O1 → OptimizationLevel.Basic
#   O2 → OptimizationLevel.Standard   (default)
#   O3 → OptimizationLevel.Aggressive
```

#### Key functions

```
fn compare_module(module: MirModule, config: CompareConfig) -> CompareReport
    # 1. optimized_module = run_pipeline(module, config)
    # 2. unopt_cpp = CCodegenAdapter.compile_module(module)      -> text
    #    opt_cpp   = CCodegenAdapter.compile_module(optimized_module) -> text
    # 3. write to temp files, shell_output clang++ to compile both
    # 4. time each binary with shell_output("time ./binary")
    # 5. optionally shell_output("perf stat ./binary") for insn counts
    # 6. return CompareReport

fn compile_cpp_to_binary(cpp_src: text, label: text) -> text?
    # writes cpp_src to {temp_dir()}/simple_cmp_{label}.cpp
    # shell_output("clang++ -std=c++20 -O2 {src} -o {out}")
    # returns binary path or nil on failure

fn time_binary(binary_path: text, runs: i64) -> i64
    # shell_output("for i in $(seq {runs}); do time {binary_path}; done")
    # parse wall-time lines, return median ms

fn perf_stat_binary(binary_path: text) -> i64?
    # shell_output("perf stat {binary_path} 2>&1")
    # parse "instructions" line; return nil if perf unavailable

fn format_compare_report(report: CompareReport) -> text
    # human-readable table used by CLI
```

#### Data flow

```
MirModule
  → run_pipeline() → optimized MirModule
  → CCodegenAdapter.compile_module() → C++ text (x2)
  → compile_cpp_to_binary() → binary paths
  → time_binary() / perf_stat_binary() → BenchResult[]
  → CompareReport
```

#### Dependencies

- `use compiler.mir_opt.mir_opt.mod.{run_typed_pass_on_module}`
- `use compiler.backend.c.c_codegen_adapter.{CCodegenAdapter}`
- `use std.io_runtime.{shell_output, write_file, temp_dir}`

No new extern calls. All shell invocations use `shell_output` (same pattern as the linker wrapper).

---

## AC-7 — General Rule Engine Extension

### File: `src/compiler/60.mir_opt/mir_opt/pattern/pattern_rule_pass.spl`

New file — the single dispatcher that executes loaded `.opt.json` rules. The existing `PatternIdiom` PassKind arm in `run_pass_on_module` is extended to call this.

#### Key types

```
# Defined here (extends rule_engine.spl concepts)

struct MirPatternSlot:
    # One position in the instruction match
    kind_tag:  text         # "BinOp" | "Copy" | "Load" | "Intrinsic" | "*"
    operand_0: text?        # literal operand or "$wildcard"
    operand_1: text?
    dest:      text?        # "$dest" wildcard

struct MirPattern:
    inst_count: i64          # always 1 for this phase
    slots:      [MirPatternSlot]

struct MirRewrite:
    kind_tag:  text          # replacement MirInstKind name, or "Remove" to delete the instruction
    dest:      text          # "$dest" — bound from match
    operands:  [text]        # literals or bound wildcards

# "Remove" in kind_tag means the instruction is dropped entirely from the block.
# This is the correct representation for self-copy elim and redundant intrinsic
# removal — there is NO "Nop" variant in MirInstKind. The apply_rewrite function
# returns nil when kind_tag == "Remove"; the caller skips adding the inst to the
# rebuilt block.

struct PatternRule:
    name:       text
    pattern:    MirPattern
    rewrite:    MirRewrite
    cost_delta: i64          # negative = cheaper; used to gate application
    safety:     text         # "pure" | "unsafe"

struct PatternRuleSet:
    source:  text            # manifest name
    rules:   [PatternRule]

struct PatternRulePass:
    rule_sets: [PatternRuleSet]
```

#### Key functions

```
fn pattern_rule_pass_new(rule_sets: [PatternRuleSet]) -> PatternRulePass

fn pattern_rule_pass_run(pass: PatternRulePass, module: MirModule) -> MirModule
    # for each function, for each block, for each inst:
    #   try_match_and_rewrite(pass.rule_sets, inst) -> MirInst?

fn try_match_and_rewrite(rule_sets: [PatternRuleSet], inst: MirInst) -> MirInst?
    # walks rule tables; first match wins; returns rewritten inst or nil

fn match_pattern_slot(slot: MirPatternSlot, inst: MirInst) -> [text: text]?
    # returns binding map {wildcard_name -> concrete_value} or nil

fn apply_rewrite(rewrite: MirRewrite, bindings: [text: text]) -> MirInst?
    # Returns nil in two cases:
    #   (a) kind_tag == "Remove" — caller drops the instruction
    #   (b) kind_tag names an unknown MirInstKind variant — safety guard, no rewrite
    # Otherwise substitutes bound wildcards and returns the replacement MirInst
```

### Schema extension: `optimizer_manifest.spl`

Add optional `rules: [PatternRule]` to `OptimizerManifest`. Loader change:

```
# Existing struct gains one field:
struct OptimizerManifest:
    ...existing fields...
    rules: [PatternRule]    # may be empty

# New helper:
fn manifest_to_pattern_rule_set(manifest: OptimizerManifest) -> PatternRuleSet
    PatternRuleSet(source: manifest.name, rules: manifest.rules)
```

### Wiring in `mir_opt/mod.spl`

In `run_pass_on_module`, extend the `PatternIdiom` arm (already exists):

```
case PatternIdiom:
    val rule_sets = session_dynamic_pass_registry_rule_sets()  # new helper
    val pass = pattern_rule_pass_new(rule_sets)
    pattern_rule_pass_run(pass, module)
```

`session_dynamic_pass_registry_rule_sets` is a new module-level function added to `optimizer_manifest.spl`:

```
# Module-level session registry (mutable singleton for the compile session)
var _session_dynamic_registry: DynamicPassRegistry? = nil

fn session_dynamic_pass_registry() -> DynamicPassRegistry:
    _session_dynamic_registry ?? dynamic_pass_registry_new()

fn session_dynamic_pass_registry_rule_sets() -> [PatternRuleSet]:
    val reg = session_dynamic_pass_registry()
    reg.manifests.map(fn(m) manifest_to_pattern_rule_set(m))
```

### Example `.opt.json` rules (3 concrete examples)

**Example 1 — strength reduction: x * 2 → x << 1**
```json
{
  "schema_version": 1,
  "compiler_abi": "simple.opt.mir.v1",
  "name": "strength-reduce-mul2",
  "version": "1.0.0",
  "min_compiler_version": "0.9.8",
  "passes": [],
  "rules": [
    {
      "name": "mul_by_2_to_shl",
      "pattern": {
        "inst_count": 1,
        "slots": [
          {
            "kind_tag": "BinOp",
            "operand_0": "$x",
            "operand_1": "ConstInt(2)",
            "dest": "$d"
          }
        ]
      },
      "rewrite": {
        "kind_tag": "BinOp",
        "dest": "$d",
        "operands": ["Shl", "$x", "ConstInt(1)"]
      },
      "cost_delta": -3,
      "safety": "pure"
    }
  ]
}
```

**Example 2 — copy elimination: copy where dest == src**
```json
{
  "schema_version": 1,
  "compiler_abi": "simple.opt.mir.v1",
  "name": "trivial-copy-elim",
  "version": "1.0.0",
  "min_compiler_version": "0.9.8",
  "passes": [],
  "rules": [
    {
      "name": "copy_self_elim",
      "pattern": {
        "inst_count": 1,
        "slots": [
          {
            "kind_tag": "Copy",
            "operand_0": "$x",
            "dest": "$x"
          }
        ]
      },
      "rewrite": {
        "kind_tag": "Remove",
        "dest": "$x",
        "operands": []
      },
      "cost_delta": -1,
      "safety": "pure"
    }
  ]
}
```
Note: `"$x"` appears as both `operand_0` and `dest` — the binding-equality rule enforces they are the same local. `"Remove"` deletes the instruction (no `Nop` variant exists in `MirInstKind`).

**Example 3 — add-zero elimination: x + 0 → copy x**
```json
{
  "schema_version": 1,
  "compiler_abi": "simple.opt.mir.v1",
  "name": "add-zero-elim",
  "version": "1.0.0",
  "min_compiler_version": "0.9.8",
  "passes": [],
  "rules": [
    {
      "name": "add_zero_to_copy",
      "pattern": {
        "inst_count": 1,
        "slots": [
          {
            "kind_tag": "BinOp",
            "operand_0": "$x",
            "operand_1": "ConstInt(0)",
            "dest": "$d"
          }
        ]
      },
      "rewrite": {
        "kind_tag": "Copy",
        "dest": "$d",
        "operands": ["$x"]
      },
      "cost_delta": -2,
      "safety": "pure"
    }
  ]
}
```

Example files live at: `src/compiler/60.mir_opt/mir_opt/pattern/examples/`
- `strength_reduce_mul2.opt.json`
- `trivial_copy_elim.opt.json`
- `add_zero_elim.opt.json`

### Dependencies

- Extends `optimizer_manifest.spl` (add `rules` field + `manifest_to_pattern_rule_set`)
- Uses `rule_engine.spl` types (`Rule`, `MatchHit`) as conceptual anchors but defines richer `PatternRule` / `MirPattern` / `MirRewrite` structs
- Wires into `mir_opt/mod.spl` `PatternIdiom` arm only — no new PassKind needed

---

## AC-8 — C-Parity MIR Passes (fill stub bodies)

All three stub bodies are wired into existing match arms in `run_pass_on_module` in `mir_opt/mod.spl`. Implementations go in **`optimization_passes.spl`** following the existing pattern (a top-level `fn` that takes `MirFunction` + `OptimizationStats`, returns `MirFunction`).

### 8a — `BoundsCheckElimination`

**IMPORTANT**: `src/compiler/60.mir_opt/mir_opt/bounds_check_elim.spl` already exists with a full `BoundsCheckElimination` class implementation (conservative same-block dedup + loop-bounds proof). The stub arm in `optimization_passes.spl` just needs to call it. Do NOT rewrite the pass — delegate to the existing class.

Existing types in `bounds_check_elim.spl`:
- `class BoundsCheckElimination` with `run_on_function(func: MirFunction) -> MirFunction`
- `class LoopBoundsProof`, `ExplicitRangeProof`, `ConstantIndexProof`
- `fn is_bounds_check_intrinsic(name: text) -> bool` — matches all 4 intrinsic name variants
- `fn bounds_check_key(name, args) -> text` — dedup key for seen-checks set

**Wire-up in `optimization_passes.spl`** — add a thin wrapper:
```
fn optimize_bounds_check_elimination(func: MirFunction, stats: OptimizationStats) -> MirFunction
    use compiler.mir_opt.mir_opt.bounds_check_elim.{BoundsCheckElimination}
    val pass = BoundsCheckElimination.new()
    val result = pass.run_on_function(func)
    stats.bounds_checks_eliminated = stats.bounds_checks_eliminated + pass.removed_checks
    result
```

**Wire-up in `mir_opt/mod.spl`** (line ~662):
```
case BoundsCheckElimination:
    optimize_function_pass(module, fn(f) optimize_bounds_check_elimination(f, ctx.stats))
```

**Before/after test**: `test/compiler/mir_opt/bounds_check_elimination_spec.spl`
- Before: two consecutive `Intrinsic(nil, "bounds_check", [%idx, %len])` with same args in same block
- After: first check retained, second removed (dropped from rebuilt block list)

### 8b — `CopyPropagation`

The pass promotes `Copy(dest, src)` → `Move(dest, src)` when `src` has no subsequent uses after this point. This avoids a redundant retain/copy in the GC path.

```
fn optimize_copy_propagation(func: MirFunction, stats: OptimizationStats) -> MirFunction
    # Pass 1: build use-count map: LocalId -> i64 (count of uses after def)
    # Pass 2: for each Copy(dest, src):
    #   if use_count[src] == 1 (this Copy is the only remaining use):
    #     replace with Move(dest, src)
    #     decrement use_count[src] to 0
    # Update stats.copy_to_move_promotions (new stats field)
```

**Wire-up** (line ~637):
```
case CopyPropagation:
    optimize_function_pass(module, fn(f) optimize_copy_propagation(f, ctx.stats))
```

**Before/after test**: `test/compiler/mir_opt/copy_propagation_spec.spl`
- Before: `%a = copy %b`, `%b` not used elsewhere after
- After: `%a = move %b`

### 8c — `LoopInvariantMotion`

Delegates Load/Call hoisting to the existing `optimize_read_ahead_hoist`. Adds generic `BinOp` and `Copy` hoisting on top.

```
fn optimize_loop_invariant_motion(func: MirFunction, stats: OptimizationStats) -> MirFunction
    # Step 1: call optimize_read_ahead_hoist(func, stats)  -- Load/Call invariants
    # Step 2: for each detected loop (back-edge heuristic: block whose successor
    #           has a lower block_id):
    #   collect header block, body blocks, pre-header block
    #   for each inst in body blocks:
    #     if inst.kind is BinOp/UnaryOp/Copy/Cast AND
    #        all operands are defined outside the loop:
    #       move inst to pre-header block
    #       update stats.loop_invariant_hoisted
```

The loop detection uses the same back-edge scan already present in `optimize_read_ahead_hoist`. **Refactor note**: first extract that scan into a shared `fn detect_loops(func: MirFunction) -> [LoopInfo]` at the top of `optimization_passes.spl`, then verify that the `ReadAheadHoist` tests still pass before adding generic BinOp/Copy hoisting on top. Do not change `ReadAheadHoist` logic during this extraction — only factor out the loop-detection sub-step.

```
struct LoopInfo:
    header_block:     BlockId
    body_blocks:      [BlockId]
    pre_header_block: BlockId?   # nil if no unique pre-header
    back_edge_src:    BlockId
```

**Wire-up** (line ~654):
```
case LoopInvariantMotion:
    optimize_function_pass(module, fn(f) optimize_loop_invariant_motion(f, ctx.stats))
```

**Before/after test**: `test/compiler/mir_opt/loop_invariant_motion_spec.spl`
- Before: `%x = binop Add %const1 %const2` inside loop body
- After: `%x` computed in pre-header; loop body gets `copy %x`

---

## AC-9 — CLI Surface

### File: `src/app/optimize/main.spl`

New file. Entry point for `bin/simple optimize`.

```
use std.io_runtime.{shell_output, print_line}
use compiler.mir.{MirModule}
use compiler.mir_opt.mir_opt.mod.{run_typed_pass_on_module, OptLevel, PassKind}
use compiler.mir_opt.optimizer_manifest.{load_manifest_v1, DynamicPassRegistry}
use compiler.mir_opt.mir_opt.pattern.pattern_rule_pass.{pattern_rule_pass_new, pattern_rule_pass_run}
use compiler.backend.c.c_codegen_adapter.{CCodegenAdapter}
use app.optimize.compare.{compare_module, CompareConfig, format_compare_report}
use compiler.tools.perf.optimizer.{OptSuggestion, analyze_code}  # reuse existing type
```

#### CLI flags

| Flag | Type | Meaning |
|---|---|---|
| `<file.spl>` | positional | Source file to optimize |
| `--compare` | bool | Run perf-comparison harness (AC-6) |
| `--apply` | bool | Write optimized MIR to `.mir.json` sidecar |
| `--passes=a,b,c` | text | Comma-separated pass names; default = level pipeline |
| `--level=O0\|O1\|O2\|O3` | text | Optimization level; default O2 |
| `--rules=path.opt.json` | text? | Load extra rule file (AC-7) |
| `--native` | bool | Add Cranelift leg to compare (AC-6 extension) |

#### Key types

```
struct OptimizeArgs:
    source_file: text
    compare:     bool
    apply:       bool
    passes:      [text]        # empty = use level default
    level:       OptimizationLevel   # parsed from --level=O0..O3 flag
    rules_file:  text?
    native_leg:  bool

struct OptimizeResult:
    suggestions: [OptSuggestion]   # reuse existing type from perf/optimizer.spl
    compare_report: CompareReport?
    applied_mir_path: text?
```

#### Key functions

```
fn parse_optimize_args(args: [text]) -> OptimizeArgs?
    # parse positional + flags; return nil on error with usage print

fn run_optimize_command(args: OptimizeArgs) -> i64
    # 1. load and compile source_file to MirModule
    # 2. if args.rules_file.?: load_manifest_v1(read_file(rules_file)) → register rules
    # 3. run pass pipeline → optimized MirModule
    # 4. collect suggestions via analyze_code(source_file)
    # 5. if args.compare: compare_module(module, config) → print report
    # 6. if args.apply: write optimized MIR JSON to {source_file}.mir.json
    # 7. print suggestion list
    # 8. return 0 on success, 1 on error

fn print_suggestions(suggestions: [OptSuggestion])
    # groups by severity; prints pass name, location, expected speedup
    # format: "[pass_name] file:line — message\n  → suggestion"
```

#### Output format

```
Optimization report: src/server/handler.spl  (O2, 3 passes)
──────────────────────────────────────────────
[BoundsCheckElimination]  handler.spl:142  — redundant bounds check
  → dominated by check at line 138; elided (cost_delta: -2)

[LoopInvariantMotion]     handler.spl:201  — loop-invariant BinOp
  → hoisted Add(%buf_size, 8) to pre-header (cost_delta: -5)

[CopyPropagation]         handler.spl:215  — copy promoted to move
  → %tmp not used after copy; promoted (cost_delta: -1)

Summary: 3 optimizations, estimated -8 cost units
```

### Wire into CLI dispatch: `src/app/cli/main_part1.spl`

Add a new `case "optimize":` arm in the top-level subcommand match block (exact insertion point: after existing `case "perf":` arm or alphabetically). Pattern matches the existing style:

```
case "optimize":
    use app.optimize.main.{parse_optimize_args, run_optimize_command}
    val opt_args = parse_optimize_args(rest_args)
    if opt_args.?:
        exit_code = run_optimize_command(opt_args.unwrap())
    else:
        print_line("Usage: simple optimize <file.spl> [--compare] [--apply] [--passes=...] [--level=O1|O2|O3]")
        exit_code = 1
```

---

## Module dependency graph

```
src/app/optimize/main.spl
  ├── src/app/optimize/compare.spl          (AC-6)
  ├── src/compiler/60.mir_opt/mir_opt/pattern/pattern_rule_pass.spl  (AC-7)
  ├── src/compiler/60.mir_opt/optimizer_manifest.spl  (extended for AC-7)
  ├── src/compiler/60.mir_opt/optimization_passes.spl  (AC-8 bodies added)
  ├── src/compiler/60.mir_opt/mir_opt/mod.spl  (arms wired AC-8, PatternIdiom AC-7)
  └── src/compiler/90.tools/perf/optimizer.spl  (OptSuggestion reused)

src/app/cli/main_part1.spl  (case "optimize" arm added)
```

---

## New files to create

| File | AC | Notes |
|---|---|---|
| `src/app/optimize/main.spl` | AC-9 | CLI entry point |
| `src/app/optimize/compare.spl` | AC-6 | Perf harness |
| `src/compiler/60.mir_opt/mir_opt/pattern/pattern_rule_pass.spl` | AC-7 | Rule dispatcher |
| `src/compiler/60.mir_opt/mir_opt/pattern/examples/strength_reduce_mul2.opt.json` | AC-7 | Example rule |
| `src/compiler/60.mir_opt/mir_opt/pattern/examples/trivial_copy_elim.opt.json` | AC-7 | Example rule |
| `src/compiler/60.mir_opt/mir_opt/pattern/examples/add_zero_elim.opt.json` | AC-7 | Example rule |
| `test/compiler/mir_opt/bounds_check_elimination_spec.spl` | AC-8 | Before/after test |
| `test/compiler/mir_opt/copy_propagation_spec.spl` | AC-8 | Before/after test |
| `test/compiler/mir_opt/loop_invariant_motion_spec.spl` | AC-8 | Before/after test |

## Files to modify

| File | AC | Change |
|---|---|---|
| `src/compiler/60.mir_opt/optimization_passes.spl` | AC-8 | Add thin wrappers for 3 pass bodies + extract `detect_loops` helper |
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | AC-7,8 | Wire 3 stub arms + PatternIdiom rule-set dispatch |
| `src/compiler/60.mir_opt/optimizer_manifest.spl` | AC-7 | Add `rules: [PatternRule]` field + `manifest_to_pattern_rule_set` + session registry helpers |
| `src/app/cli/main_part1.spl` | AC-9 | Add `case "optimize":` arm |

## Pre-existing files (no new creation needed)

| File | AC | Role |
|---|---|---|
| `src/compiler/60.mir_opt/mir_opt/bounds_check_elim.spl` | AC-8a | Full BCE implementation — delegate to it, do not rewrite |
