# Option-truthiness (`Some(0)`-falsy) landmine sweep — compiler source

Scope: `src/compiler/**` (Rust seed / vendor / `src/lib` excluded per task).
Worktree: `/tmp/wt_optsweep` @ `f10db44f0f477e839562654672a1531d58c881c4`.
Excluded from edits per instructions: `switch_operators_calls.spl`,
`method_calls_literals.spl`, `mir_lowering_stmts.spl`, `parser_stmts.spl`,
`primary_expr.spl`, `70.backend/**` (owned by parallel lanes) — no class-(a)
bugs were found living exclusively in those files; see "70.backend notes"
below for what was seen there.

## Method

1. Grepped `src/compiler` for `fn ... -> (i64|i32|u64|u32|usize|isize)?` and
   `: (i64|...)?` field/param declarations to enumerate every Option-of-integer
   type (42 function signatures, 42 declarations).
2. For each, grepped every call site and classified the boolean test used:
   - `if x.?:` / `while x.?:` / `if val y = x.?:` (calls the `.?` operator in a
     boolean-testing position) → **class (a) if the payload can be 0**, since
     `.?` truthiness on a boxed `i64?` collapses `Some(0)` to falsy in the
     bootstrap seed interpreter (confirmed root cause of the already-landed
     `var_reassign_written_local` fix).
   - `if val y = x:` (pattern-bind directly on an already-Option value, no
     `.?` suffix) → **class (c), safe** — this is a direct tag match with no
     `.?` call in the boolean position, so it does not hit the collapse.
   - Option-of-struct/enum/text (`LocalId?`, `MirOperand?`, `text?`, …) →
     **class (c), safe** regardless of `.?` usage, since the bug is specifically
     about the unwrapped *integer* payload aliasing C-style falsy zero, not
     about tag presence.
3. Separately grepped `if val Some(` combined with `.get(` to find the
   documented sibling bug (`Dict.get()` returns the raw value or nil, not a
   `Some(..)`-tagged Option — `if val Some(x) = dict.get(k):` never matches;
   documented in `src/lib/nogc_sync_mut/diag.spl` header).

## Fixed (class a) — 13 sites across 11 files

All fixes mirror the landed style: replace the truthy test with an explicit
`match ... case Some(x): ... case nil: ...` (or, for `Dict.get()` misuse, a
direct `!= nil` check per the diag.spl guidance).

| # | File:line (pre-fix) | Bug | Severity / why payload-0 is reachable |
|---|---|---|---|
| 1 | `60.mir_opt/mir_opt/var_reassign_ssa.spl` `ssa_max_local_from_operand` | `if local.?:` on `var_reassign_operand_local()` (local id) | max-local-id scan; local id 0 silently excluded from renumbering base |
| 2 | same file `ssa_max_local_from_inst` | `if written.?:` on written-local id | same max-id-scan family |
| 3 | same file `ssa_block_written_locals` | `if written.?:` | feeds phi-merge "common written locals" — same class as the original bug, different call path |
| 4 | same file `ssa_apply_phi_plan_to_block` (via `ssa_phi_plan_pred_value_for_block`) | `if pred_value.?:` on predecessor's incoming local id | if pred value is local 0, phi source rewrite for that predecessor is silently skipped |
| 5 | same file `ssa_reassigned_locals_for_blocks` | `if written.?:` | feeds the multi-def/alloca-slotting decision — the exact class of miscompile the landed fix addressed, different call path |
| 6 | same file `ssa_operand_push_local` | `if lo.?:` on operand's local id | feeds cross-block-live-use collection |
| 7 | same file `ssa_local_defined_in_block` | `if written.?:` | feeds cross-block-live def-check (conservative-safe direction, still same landmine) |
| 8 | `60.mir_opt/mir_opt/var_reassign_analysis.spl` `var_reassign_collect_escape_operand`(`_with_aliases`) | `if local.?:` | escape-analysis: missing an escape for local 0 could make an escaping local 0 look SSA-transform-safe when it is not |
| 9 | same file `var_reassign_update_aliases_for_inst` default case | `if written.?:` | stale alias info for local 0 |
| 10 | same file `analyze_var_reassign_blocks` (core reassignment-count scan) | `if written.?:` | **highest severity in this file**: under-counts reassignments of local 0, could report `ssa_transform_safe=true` for an actually-unsafe transform |
| 11 | `55.borrow/gc_analysis/mod.spl` `process_instruction` (SetField/GetField/Call-arg) | `if val x = y.?:` (pattern-bind form, still calls `.?`) | **GC correctness**: missing a field-store/field-load/call-arg escape record for local 0 → missed write barrier or missed GC root registration |
| 12 | `95.interp/mir_interpreter.spl` + `95.interp/mir_interp_ops.spl` `execute_call`-style loop | `while self.current_block.?:` | **highest severity overall**: block id 0 is the conventional entry-block id; if this interpreter path is reachable with block 0 as current, the execution loop exits before running a single instruction |
| 13 | `95.interp/mir_interpreter.spl` `_execute_intrinsic` (`__simple_ssa_phi`) | `if self.previous_block.?:` | if predecessor block is id 0, the phi lookup silently falls through to the `args[1]` fallback value instead of the value actually paired with predecessor 0 — genuine silent-wrong |

Also fixed, same class, lower severity (miss is conservative/safe-direction —
skips an optimization rather than mis-applying one), fixed for consistency
since they're the identical pattern and cheap:

- `60.mir_opt/mir_opt/bounds_check_elim.spl`: `try_match_loop_guard_inst` (`if val index_id = idx_id:`/`if val array_id = arr_id:` via `operand_local_id_raw`), `inst_is_positive_add_of_self` (`if val self_id = self_ref:`).
- `60.mir_opt/mir_opt/collection_opt_patterns.spl`: `colopt_detect_linear_scan_guard` (`if idx.? and arr.?:`), `colopt_block_increments_index` (`if src.?:`).
- `60.mir_opt/mir_opt/_Inline/driver.spl`: callee-by-symbol-id resolution (`if callee_id.?:`) — falls back to name-based lookup on miss.
- `30.types/dim_constraints.spl` `unify` fallback case: `if v1.? and v2.?:` — a dimension expression can legitimately evaluate to 0; the bug would falsely report a dimension **mismatch compile error** for two dims that both evaluate to 0 (this one is a user-visible false-positive error, not just a missed optimization).
- `60.mir_opt/mir_opt/loop_detect.spl`: `analyze_trip_count` (`if bound.?:`), `extract_comparison_bound` (`if not cond_local_id.?:`, `if const_val.?:`, `if const_val_l.?:`) — constant trip count / comparison bound of 0 is legitimate.

## Sibling bug: `Dict.get()` + `if val Some(x) =` (never matches) — 4 sites fixed

Per the documented landmine in `src/lib/nogc_sync_mut/diag.spl` header
("`Dict.get()` returns the raw value or nil, NOT a `Some(..)`-tagged Option").
Confirmed by checking each receiver's declared type is a Dict literal
(`{K: V}` / `Dict<K, V>`):

- `00.common/effects.spl` `EffectEnv.get_effect` — **high severity**: both
  `self.effects.get(sym)` (inferred effects) and `self.builtins.get(sym)`
  (SFFI builtin effects) used the never-matching pattern, so `get_effect`
  always fell through to the `Synchronous` default — inferred/builtin effect
  annotations were silently never consulted.
- `99.loader/module_resolver/manifest.spl` — the manifest **cache** check
  never matched, so every call reparsed `__init__.spl` from scratch (perf,
  not correctness, but the doc'd "returns cached manifest if available"
  behavior was dead code).
- `99.loader/module_resolver/resolution.spl` — same pattern for collecting
  `common_uses` from parent-directory manifests.

Fixed with a direct `!= nil` check (both the value type here is a
struct/enum, not int, so no `Some(0)` concern — this is purely the
tag-vs-raw-value representation bug).

## Deferred / documented only (not fixed)

- **`70.backend/**`** (excluded per instructions). Notable finding while
  scanning for context: `_MirToLlvm/core_codegen.spl` already documents and
  works around a **different, related but distinct** interpreter bug
  (`match dict.get(): case Some(ty)/nil` mis-dispatching under the seed
  interpreter — bug #134/#135), using `if maybe_ty.?: ... .unwrap()` instead
  of `match`. That workaround is safe for `text?`-payloads (no zero-payload
  concern) — no action needed, left as-is.
- `70.backend/backend/llvm_lib_translate_expr.spl:641` `ssa_phi_const_block_arg`,
  `70.backend/backend/cranelift_codegen_adapter.spl:554`
  `cranelift_phi_const_block_arg`, `70.backend/backend/cranelift_gemm_fusion.spl:17`
  `operand_copy_local_id`, `70.backend/backend/codegen_enhanced.spl:69`
  `local_id: i64?` — all return/hold local ids (0 is reachable) and are
  candidates for the same class-(a) fix; **not touched** (file scope
  exclusion). Flagging for a follow-up in a 70.backend-owned lane.
- `30.types/type_check/mod.spl:74` `if val Some(ty) = types.get(...)`: `types`
  is a local type alias `TypeRegistry = SymbolTable`, and `SymbolTable` has no
  `.get()` method in `20.hir/hir_types.spl` (only `symbols`/`scopes` Dict
  fields and a `define()` method) — could not confirm this call site even
  resolves/compiles as written; left undisturbed pending clarification
  (possibly dead code).
- `30.types/_TypeLayout/arch_and_verify.spl:159` `compute_field_offset(...) ->
  i64?` (field offset 0 for the first struct field is clearly reachable) has
  **no callers anywhere in `src/compiler`** — dead/unreached, not fixed.
- `99.loader/jit_instantiator.spl` / `module_loader.spl` `.lookup(...)` and
  `99.loader/loader/compiler_sffi.spl` `sffi_json_field_i64` were reviewed at
  the signature level only (call sites use the value directly rather than a
  `.?` truthiness gate) — no truthy-test misuse found, not touched.
- `60.mir_opt/mir_opt/loop_strength.spl` `operand_const_int_value`/
  `const_log2` and `60.mir_opt/_OptimizationPasses/engine.spl`
  `log2_if_power_of_2`: callers use `if val shift_value = shift_amt:` (no
  `.?` suffix — direct Option pattern-bind, **class (c) safe** per the
  distinction established above) — reviewed, no fix needed.

## Verification

- Two hand-written control programs, built and run via the fixed worktree's
  `bin/simple native-build` (interprets `src/compiler/*.spl` directly, so
  edits take effect immediately):
  - `classify`/`sum_loop` (value-returning fns, if/elif/else + while-loop
    reassignment): output `pos`, `neg`, `45` — all correct.
  - `maybe_print`/`loop_sum_void` (Unit-returning fns — per the landed fix's
    own comment, a Unit function's first real temp reliably lands on local id
    0, which is the exact scenario this whole sweep targets): output `yes`,
    `nope`, `10` — all correct, RC=0.
- Full smoke matrix: `sh scripts/check/native-smoke-matrix.shs` →
  **14/15 pass, 0 codegen_fallback_hits**, sole failure is the pre-existing
  `option_nil_check` case (matches the task's stated allowed-failure gate
  exactly). Full output: `scratchpad/smoke_matrix_output.txt`.

## Deliverables

- Patch: `scratchpad/opt_truthiness_sweep.patch` (13 files, 387 insertions / 220 deletions)
- This report: `scratchpad/opt_truthiness_sweep_report.md`
- Worktree `/tmp/wt_optsweep` removed after patch export (per instructions —
  no commit/push).
