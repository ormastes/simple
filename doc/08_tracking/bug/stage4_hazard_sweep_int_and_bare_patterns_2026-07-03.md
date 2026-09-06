# Stage4 Hazard Audit: int(text) & Bare Enum-Variant Patterns
**Date:** 2026-07-03  
**Scope:** Audit sweeps per iteration-18 hazard list (mechanical portion only)

## Summary
- **Sweep 1 (int(text) calls):** 40+ affected sites found (text arguments to int())
- **Sweep 2 (bare case patterns):** 3 sites found; 1 fixed (outside excluded dirs)
- **Excluded dirs checked but NOT EDITED:** src/compiler/20.hir/, src/compiler/80.driver/

---

## SWEEP 1: int(text) Affected Call Sites

### Root Cause
Stage4 codegen bug: `int(text_arg)` returns first char code instead of parsing decimal.
Workaround: `parser_guarded_int_text()` has manual decimal-loop parse.

### Affected Sites (Text Arguments)

| File | Line | Pattern | Context |
|------|------|---------|---------|
| src/compiler/10.frontend/core/interpreter/mod.spl | 207 | `int(env_threshold)` | env var parse |
| src/compiler/10.frontend/parser_extensions.spl | 94 | `int(self.current().text)` | token text → int |
| src/compiler/10.frontend/core/type_checker.spl | 335 | `int(compare_val)` | string predicate parse |
| src/compiler/10.frontend/core/type_checker.spl | 405 | `int(compare_str)` | string predicate parse |
| src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl | 181 | `int(oc)` | octal char → digit |
| src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl | 92 | `int(exp_val)` | loop bound parse |
| src/compiler/10.frontend/core/interpreter/eval_calls.spl | 72 | `int(exp_val)` | loop bound parse |
| src/compiler/90.tools/verify/docker_setup.spl | 155 | `int(di_lines)` | command output parse |
| src/compiler/90.tools/verify/docker_setup.spl | 165 | `int(compose_lines)` | command output parse |
| src/compiler/90.tools/duplicate_check/benchmark.spl | 155–159 | `int(parts[1..5])` | log fields parse |
| src/compiler/90.tools/duplicate_check/_Detector/interner_and_logging.spl | 58 | `int(parts[1])` | memory stats parse |
| src/compiler/90.tools/duplicate_check/parallel.spl | 33 | `int(output)` | command output parse |
| src/compiler/90.tools/duplicate_check/main.spl | 123–138 | `int(args[...])` | CLI arg parse |
| src/lib/gc_async_mut/play/locator.spl | 70 | `int(num_str)` | string parse |
| src/lib/gc_async_mut/pure/metrics.spl | 173 | `int(true_class)` | string parse |
| src/lib/gc_async_mut/pure/nn/serialization.spl | 149, 155, 288, 291 | `int(num_str)` | model shape parse |
| src/lib/gc_async_mut/src/exp/query.spl | 109 | `int(step_str)` | step param parse |
| src/lib/gc_async_mut/src/exp/run.spl | 242 | `int(step_str)` | step param parse |
| src/lib/nogc_async_mut/config_parser.spl | 146 | `int(str_val)` | config parse |
| src/lib/nogc_async_mut/debugger.spl | 251, 264 | `int(loc_parts[1])` | source loc parse |
| src/lib/nogc_async_mut/process_monitor.spl | 292 | `int(s)` | string parse |
| src/lib/nogc_async_mut/resource_tracker.spl | 385 | `int(s)` | string parse |
| src/lib/nogc_async_mut/mcp/*.spl | (8 sites) | `int(trimmed)`, `int(t)`, `int(line_str)` | protocol/tool parsing |
| src/lib/nogc_async_mut/llm/config.spl | 162 | `int(value)` | config parse |
| src/lib/nogc_async_mut_noalloc/baremetal/*.spl | (4 sites) | `int(timeout_str)`, `int(code_str)`, `int(cycles_str)` | runner parse |

**Total affected:** ~40+ call sites identified.  
**Risk:** All require manual decimal-loop workaround or parser-guarded variant until stage4 fix lands.

---

## SWEEP 2: Bare Enum-Variant Pattern Matches

### Root Cause
Stage4 compiler bug: `case Bare:` matches irrefutably (always true) when a struct named `Bare` exists.
Fix: Qualify to `case EnumName.Bare:` using enum name obvious from match scrutinee.

### Sites Found

| File | Line | Pattern | Match Scrutinee | Struct Conflict | Status |
|------|------|---------|-----------------|-----------------|--------|
| src/lib/nogc_sync_mut/driver/loader.spl | 207–229 | `case Block:`, etc. | `c: DriverClass` & `k: ManifestKind` | `struct Block` exists | **FIXED** |
| src/lib/nogc_async_mut/driver/loader.spl | 207–229 | `case Block:`, etc. | `c: DriverClass` & `k: ManifestKind` | `struct Block` exists | **FIXED** |
| src/app/interpreter/collections/persistent_symbol_table.spl | 277 | `case Field:` | `self: SymbolKind` | `struct Field` exists | **FIXED** |

**Total affected:** 3 sites (all fixed)  
**Excluded dirs (NOT EDITED):** None  
**Fixed sites:** 3 sites

### Fixed Site Details

**File 1:** src/lib/nogc_sync_mut/driver/loader.spl:207–229
- `kind_to_byte(k: ManifestKind)`: `case Driver:` → `case ManifestKind.Driver:`; `case NativeLib:` → `case ManifestKind.NativeLib:`
- `class_to_byte(c: DriverClass)`: All 16 variants qualified (Block→DriverClass.Block, Char→DriverClass.Char, etc.)

**File 2:** src/lib/nogc_async_mut/driver/loader.spl:207–229
- Identical changes (fork consistency maintained)

**File 3:** src/app/interpreter/collections/persistent_symbol_table.spl:277
**Change:** `case Field:` → `case SymbolKind.Field:`  
**Reason:** Match scrutinee is `self: SymbolKind`; struct `Field` exists in codebase causing ambiguity  
**Verification:** All files lint clean; loader qualification fixes verified (exit 0)

---

## Recommendations

1. **int(text) sites:** Defer mass-rewrite pending stage4 fix; may be safer to add compiler guard or use workaround where critical
2. **Bare patterns in excluded dirs:** Handled by owning lane (20.hir/80.driver owners)
3. **Follow-up:** Run full lint pass after stage4 fixes to catch any codegen fallout

