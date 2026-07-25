# Dict fundamentals on the native --entry path — characterization + fix

Worktree: `/tmp/wt_dict` @ 228ed617cad. Sanity (`print(41)`) built and ran clean.
Oracle: `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl` (interp). Native: `env -u SIMPLE_BOOTSTRAP bin/simple native-build p.spl -o bin`.
Native print has no newlines; results below concatenate (e.g. "3326" = 3,3,2,6).

## Root cause of `.len()` == 0

`Dict.len()` reaches `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
(`lower_method_call`, the `method == "len"` block, ~line 182). Two independent gaps
combine:

1. HIR type inference never populates `receiver.type_` for a `Dict`-typed local
   at this call site (same root gap already documented inline as #137/#138 for
   Array), so `len_runtime_symbol_for_hir_type` (which DOES correctly map
   `Dict(_,_) -> "rt_dict_len"`, confirmed by reading the function) never runs
   — it's dead code in this path. `resolution` also comes back `Unresolved`.
2. The `Unresolved` fallback unconditionally forces `len_symbol = "rt_len"`.
   `rt_len` (`src/runtime/runtime_native.c:821`) only special-cases
   `rt_core_as_string` and `rt_core_as_array`; a dict handle matches neither
   and falls through to a hardcoded `return 0`. Confirmed via LLVM IR dump
   (`SIMPLE_KEEP_LLVM_IR=1`): the emitted call was `call i64 @rt_len(i64 %l2)`,
   never `@rt_dict_len` — even though `rt_dict_len` is already a real, linked,
   backend-declared runtime symbol (`src/runtime/runtime_native.c:2458`;
   declared in `llvm_backend.spl`, `llvm_backend_tools.spl`,
   `llvm_lib_translate.spl`). No runtime rebuild needed — purely a compiler
   routing bug.

Array `.len()` happens to still work today only because `rt_len`'s array
branch is correct; Dict has no such luck.

## Fix (CONFLICT-FLAGGED — touches an owned/fenced file)

`method_calls_literals.spl` is on the fence list (owned by another lane) and
is the ONLY place this dispatch logic lives — per instructions this is
delivered as a flagged diff, not silently merged. Patch:
`scratchpad/dict_native.patch` (25 lines, one file).

The fix reorders the `Unresolved` branch to lower the receiver first, then
consult `self.runtime_dict_locals` (a `Dict<i64, bool>` already tracked by the
MIR-lowering layer, defined in `mir_lowering_types.spl` — NOT fenced,
populated at every dict-literal/assignment site independent of HIR static
typing) keyed by the lowered local id. If the local is known-dict, emit
`rt_dict_len` instead of `rt_len`. Array/string behavior is untouched (falls
through to the existing `rt_len` path unchanged) — verified no regression.

**Please coordinate before landing**: another lane may be mid-edit on this
same file/function.

## Characterization matrix (oracle vs native, post-fix)

| # | Case | Oracle | Native | Verdict |
|---|------|--------|--------|---------|
| 1 | `Dict<text,i64>` insert + read | 5 | 5 | CORRECT |
| 2 | Dict literal `{"x":1,"y":2}` construct+read | 1,2 | 1,2 | CORRECT |
| 3 | `.len()` after inserts, `{text:i64}` sugar type | 2 | 2 | CORRECT (was 0, now fixed) |
| 4 | `.len()` after inserts, `Dict<text,i64>` type | 2 | 2 | CORRECT (was 0, now fixed) |
| 5 | `.len()` on empty dict | 0 | 0 | CORRECT |
| 6 | `Dict<i64,i64>` int keys, insert+read+len | 10,20,2 | 10,20,2 | CORRECT |
| 7 | Array `.len()` regression check | 3 | 3 | CORRECT (unchanged) |
| 8 | `d.has("a")` / `d.has("z")` | true,false | — | LOUD-FAIL: "unresolved method call: has" (pre-existing, Task #145 gate; out of scope) |
| 9 | `d.get(k) ?? -1` | (oracle itself questionable: 40/-1) | — | LOUD-FAIL: "unresolved method call: get" (pre-existing; out of scope) |
| 10 | Overwrite existing key + len | 9,1 | 9,1 | CORRECT |
| 11 | Two independent dict locals, each `.len()` | 1,2 | 1,2 | CORRECT |
| 12 | `for k in d.keys():` | a,b | — | LOUD-FAIL: "unresolved method call: keys" (pre-existing; out of scope) |
| 13 | `for key, value in d.items():` | oracle itself errors ("Function 'items' not found") | parser error (multi-bind `for a,b in` not supported) | LOUD-FAIL both sides; feature not implemented on either path — not a native-specific regression |
| 14 | MULTI-CONSTRUCT: dict + array + while-loop combined | 3,3,2,6 | 3,3,2,6 | CORRECT |
| 15 | Missing-key raw read `d["z"]` (no `.get`) | 3 (garbage) | 0 (garbage) | SILENT-WRONG both sides, pre-existing, unrelated to this fix — **flagging as a separate bug, not fixed here** |

Bonus (found during characterization, NOT part of the len() fix, confirmed
pre-existing by diffing against unpatched `228ed617cad`): `Dict<text, text>`
(text-typed values) reads back garbage on the native path
(`d["name"] = "Alice"; print(d["name"])` prints a garbled large integer, not
"Alice") — a distinct dict-value-tagging bug, out of scope for this task,
worth filing separately.

## Verify summary

- Battery: all `.len()`-touching cases now oracle-equal (5/5).
- MULTI-CONSTRUCT (dict+array+loop combined): oracle-equal.
- No regression to array `.len()`.
- 4 pre-existing LOUD-FAILs (has/get/keys/items) — untouched, correctly loud
  not silent, out of scope per task (targeted at `.len()`).
- 2 pre-existing SILENT-WRONG bugs found and documented but NOT fixed
  (missing-key raw read, text-valued dict read) — orthogonal to `.len()`,
  confirmed present before this patch via diff against 228ed617cad.

## Deliverables

- `/home/ormastes/dev/pub/simple/scratchpad/dict_native.patch` — CONFLICT-FLAGGED diff to `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
- `/home/ormastes/dev/pub/simple/scratchpad/dict_native_report.md` — this report
- Worktree `/tmp/wt_dict` removed after patch export
