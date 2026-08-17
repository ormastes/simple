# Bug: AST env-var backing store causes O(N²) parse time

**ID:** ast_env_var_quadratic_parse_2026-06-13  
**Severity:** P1 — `check` on 400+ top-level functions times out (>300 s)  
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Reported:** 2026-06-13

---

## Empirical Data

| Functions (N) | `check` wall time | `lex`-only |
|---------------|------------------|------------|
| 100           | 52 s             | 0.25 s     |
| 200           | 146 s            | 0.58 s     |
| 400           | timeout (>300 s) | 0.99 s     |

Lexer is linear and fast — ruled out. Type inference is also ruled out (see §Secondary Suspects). Root cause is in the parser/AST layer.

---

## Root Cause: O(N²) env-var store

### Primary site

**Files:**
- `/home/ormastes/dev/pub/simple/src/compiler/10.frontend/core/ast_stmt.spl` — `stmt_alloc()`
- `/home/ormastes/dev/pub/simple/src/compiler/10.frontend/core/ast_part1.spl` — all `decl_add_*` constructors
- `/home/ormastes/dev/pub/simple/src/compiler/10.frontend/core/ast_part2.spl` — `module_add_decl()`

### Mechanism

Every AST node write calls `rt_env_set` → libc `setenv()`, AND every AST node read calls `rt_env_get` → libc `getenv()`. On Linux, both functions perform a **linear scan of the `environ[]` array**. As parsing proceeds, the environ array accumulates one entry per field per statement:

```spl
# ast_stmt.spl — stmt_alloc() (lines ~148-164)
fn stmt_alloc(tag: i64, span_id: i64) -> i64:
    val idx = stmt_count_env()           # rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT")  ← O(env_size)
    stmt_count_set(idx + 1)              # rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", ...) ← O(env_size)
    stmt_tag.push(tag)                   # array write — O(1)
    ...
    stmt_i64_set(idx, "TAG", tag)        # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_TAG", ...) ← O(env_size)
    stmt_i64_set(idx, "SPAN", span_id)   # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_SPAN", ...)← O(env_size)
    stmt_i64_set(idx, "EXPR", -1)        # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_EXPR", ...)← O(env_size)
    stmt_text_set(idx, "NAME", "")       # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_NAME", ...)← O(env_size)
    stmt_i64_set(idx, "TYPE", 0)         # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_TYPE", ...)← O(env_size)
    stmt_list_set(idx, "BODY", [])       # rt_env_set("SIMPLE_BOOTSTRAP_STMT_N_BODY", ...)← O(env_size)
```

Six `rt_env_set` calls per statement, each scanning the full environ. After parsing K statements, `environ` holds ~6K `SIMPLE_BOOTSTRAP_STMT_*` entries. Each subsequent call costs O(6K). Total:

```
Σ_{k=0}^{N·S} 6k  =  O((N·S)²)
```

For N=400 functions × S≈8 stmts each: environ grows to ~19,200 entries; the last `setenv` scans all of them. Both the **write side** (setenv during parse) and the **read side** (getenv in `flat_ast_to_module`) are O(N²) independently.

Additionally, readers always check env var first, even though arrays are also populated:

```spl
# All readers are env-first — array path is dead in practice:
fn stmt_get_tag(idx: i64) -> i64:
    val direct = rt_env_get(stmt_key(idx, "TAG")) ?? ""
    if direct != "":
        return stmt_parse_i64(direct)   # ← always taken; O(env_size) scan
    val fallback = stmt_tag[idx]        # ← dead path
    fallback
```

Same pattern in `decl_get_name`, `decl_get_ret`, `ast_module_decl_count_get`, `module_decl_at`, and all expression accessors.

---

## Why this is NOT bootstrap-only

The env-var mirror was added because module-level arrays are zero-initialized (BSS) in compiled binaries rather than running their initializers. The fix — `ast_reset()` → `stmt_reset()` — nil-guards and clears these arrays before any use. This nil-guard **is called** at `parser.spl:205` before every parse. The arrays are therefore **reliably populated** in compiled stage4 non-bootstrap mode. The env-var writes are redundant overhead in this path.

---

## Minimal Fix Proposal

### Approach: compile-time guard, array-primary readers

**Condition for safety:** The fix is safe because `parser.spl` calls `ast_reset()` before parsing, which calls `stmt_reset()` (nil-guards + clears arrays). This makes arrays valid. The env-var mirror is only needed for the true bootstrap path (`SIMPLE_BOOTSTRAP=1`) where the compiler is invoked to compile itself and the arrays may not be available.

**Three changes required:**

#### 1. Eliminate env-var writes in `stmt_alloc` for non-bootstrap path

```spl
fn stmt_alloc(tag: i64, span_id: i64) -> i64:
    val idx = stmt_count_env()
    stmt_count_set(idx + 1)
    stmt_tag.push(tag)
    stmt_span.push(span_id)
    stmt_expr.push(-1)
    stmt_name.push("")
    stmt_type_tag.push(0)
    stmt_body.push([])
    # REMOVE: all stmt_i64_set / stmt_text_set / stmt_list_set calls
    idx
```

The `stmt_count_set` call also needs guarding (it does `rt_env_set` for the count). Replace `stmt_count_env()` with `stmt_tag.len()` for the non-bootstrap read; write count only to env when in bootstrap mode.

#### 2. Make all readers array-primary (env as fallback for bootstrap)

```spl
fn stmt_get_tag(idx: i64) -> i64:
    if idx < stmt_tag.len():
        return stmt_tag[idx]            # O(1), always valid post-reset
    val direct = rt_env_get(stmt_key(idx, "TAG")) ?? ""
    stmt_parse_i64(direct)              # bootstrap fallback only
```

#### 3. Remove the 128-slot cap in `module_add_decl` (ast_part2.spl)

```spl
fn module_add_decl(decl_idx: i64):
    val count = ast_module_decl_count_get()
    module_decl_slots.push(decl_idx)   # no cap; array always valid post-reset
    ast_module_decl_count_set(count + 1)
```

Currently uses `if count < 128: module_decl_slots[count] = decl_idx` with an array of fixed 128 slots. Replace with an unbounded `push`. For N>128, `module_decl_at(i)` currently falls back to `rt_env_get` — this adds a second O(N²) site for large files.

**Apply same pattern to all `decl_*` and `expr_*` constructors/readers in `ast_part1.spl`.**

### Correctness notes

- `ast_reset()` must continue to be called before each parse invocation (already done at `parser.spl:205`)
- The env-var write path must remain active when `SIMPLE_BOOTSTRAP=1` (the bootstrap mode where the seed compiler parses its own source without compiled arrays)
- `stmt_count_env()` is used in 3 other places besides `stmt_alloc`; switch those to `stmt_tag.len()` in non-bootstrap mode
- The nil-guards in `stmt_reset()` must remain; compiled binaries do BSS-zero module-level vars

### Expected improvement

Eliminating 6×O(N·S) `setenv` calls per parse and converting all reads to O(1) array access reduces the parse phase from O(N²) to O(N). Based on the empirical curve (52s→146s→timeout for N=100→200→400), this should bring N=400 from >300s to ~1-2s.

---

## Secondary Suspects (not active in `check` path)

### `generalize_all` / `env_free_var_ids` in type inference

**File:** `/home/ormastes/dev/pub/simple/src/compiler/30.types/type_infer/generalization.spl`

`env_free_var_ids()` (line 91) scans all N entries of `HmInferContext.env` per function generalization; `to_generalize.contains(id)` is O(N) per variable. Together: O(N²) per module. `generalize_all` calls this at line 127.

This is a **real latent quadratic** — it will become the bottleneck once the env-var issue is fixed and `infer_module` is actually wired up to the driver pipeline. Currently `infer_module` is defined (`inference_control.spl:594`) but **never called** from the check/compile driver path (`type_check_impl` is a documented stub no-op; `lower_and_check_impl` creates empty HIR shells for non-bootstrap single-file input). Not the active bottleneck today.

Fix when it becomes active: replace the `[i64]` linear-scan containers (`to_generalize.contains`, `scheme.vars.contains`) with `Dict<i64, bool>` sets. Both `env_free_var_ids` and `generalize` become O(N·depth) rather than O(N²).

---

## 2026-08-01 — The env mirror is also a LEAK and an ORDER-DEPENDENCE bug

The 2026-06-13 analysis above treated this store purely as a *speed* problem and
fixed it by **gating the writes** (`expr_env_mirror_enabled()` /
`stmt_env_mirror_enabled()` / `ast_decl_env_mirror_enabled()`). That left a
second, worse defect untouched: **nothing ever removes the entries.**

This is a member of the "reset under live state" family — state reset at the
wrong moment relative to live readers.

### Mechanism

`expr_reset()` / `stmt_reset()` / `ast_reset()` clear the backing *arrays* and
set the counts to 0, but never unset a single `SIMPLE_BOOTSTRAP_EXPR_<idx>_<f>`,
`SIMPLE_BOOTSTRAP_STMT_<idx>_<f>`, `SIMPLE_BOOTSTRAP_DECL_<idx>_<f>` or
`SIMPLE_BOOTSTRAP_MODULE_DECL_<idx>` key. Every reader in this family is
**env-FIRST, array-fallback**. So after a large file is parsed, the entries for
its high indices stay alive, and the *next, smaller* file's readers are served
the **previous file's node** for any index that file never allocated.

Two consequences:

1. **Order-dependent verdicts.** The result for file B depends on whether a
   larger file A was parsed before it in the same process. Any census or sweep
   that calls `parse_module_silent_checked` repeatedly in one process has a
   result that depends on the order it walked the tree.
2. **Unbounded environ growth.** ~11 entries per expr node, 7 per stmt node and
   up to 29 per decl node, for the whole run, never freed.

**The staleness BYPASSES the guard meant to catch it.** `ast_gen_check_index`
(the L6 arena-generation check) only sees indices that carry a *minted
generation*. An env read carries none, so the guard matches and binds while the
stale value flows through unchecked — present, and inert.

**The decl half is NOT gated on `SIMPLE_BOOTSTRAP`.** `ast_decl_text_set` writes
`NAME` / `PARAM_NAMES` / `PARAM_TYPES` / `TYPE_PARAMS` / `BODY` / `IMPL_TRAIT`
whenever `not ast_decl_prefer_arena()`, i.e. on the ordinary lint/census path
with no bootstrap env set at all. The clear is therefore gated the same way, not
on `ast_decl_env_mirror_enabled()` — gating the clear more narrowly than the
write is exactly how this fix would have shipped present-but-inert.

### Fix

`expr_env_mirror_clear()` (`_AstExpr/nodes.spl`), `stmt_env_mirror_clear()`
(`ast_stmt.spl`) and `ast_decl_env_mirror_clear()` (`_Ast/decl_nodes.spl`),
called from the top of the corresponding reset, before the arrays are cleared.

Each keeps a **high-water slot** of the largest index ever mirrored since the
last reset. Without it, `*_count_set(0)` inside the reset erases the only record
of how far the mirror reaches, and a smaller file parsed after a bigger one
leaves the big file's tail entries alive — the fix would then be present and
inert for precisely the case that produces the bug.

Field lists are returned by a `fn`, not held in a module-level `val`: module
globals are nil/zero in native builds, which would make the clear silently do
nothing.

This is **not** a perf regression. The removals are the same
O(nodes x fields) order the writes already pay, and because environ now stays
bounded by ONE file instead of the cumulative run, every subsequent libc
`setenv`/`getenv` linear scan gets *cheaper*.

### Evidence (interpreter, `bin/simple run`, SIMPLE_BOOTSTRAP=1)

Probe: parse a 90-decl/180-expr file, then a 1-decl/3-expr file, in one process;
count surviving `SIMPLE_BOOTSTRAP_EXPR_<i>_TAG` and
`SIMPLE_BOOTSTRAP_DECL_<i>_NAME` + `SIMPLE_BOOTSTRAP_MODULE_DECL_<i>` keys.

| | after big file | after small file |
|---|---|---|
| expr keys, before fix | 180 | **180** (should be 3) |
| expr keys, after fix | 180 | **3** |
| decl keys, before fix | 180 | **180** (should be 2) |
| decl keys, after fix | 180 | **2** |

RED was produced by sabotaging the *implementation* (removing the
`ast_decl_env_mirror_clear()` call from `ast_reset`), not a shim; the expr
counter stayed at its fixed value of 3 during that run, proving the two clears
are independent and neither is carrying the other.

### Four zero-call-site resets — RESOLVED 2026-08-02 (all four DELETED)

`intern_reset()`, `mono_cache_reset()`, `alloc_inference_reset()` and
`bootstrap_fn_ret_types_reset()` were filed here as "accumulators with a reset
function that nothing ever calls".

The zero-call-site claim is **PROVED** for all four — a repo-wide
`/usr/bin/grep` returns 16 lines total: 4 definitions, 3 export re-exports, 4
lines inside two fully commented-out dead specs, and this doc. No `.rs`
definition exists for any of them; all four are `.spl`-only.

The implied defect, however, does **not** hold. Wiring them was the wrong fix in
every case, so all four were deleted (repo rule: implement or delete).

| reset | disposition | why |
|---|---|---|
| `intern_reset` | deleted | whole module vestigial — `intern()`/`intern_resolve()` themselves have 0 callers and `intern.spl` is not exported by any `__init__`; nothing writes the state at runtime |
| `mono_cache_reset` | deleted | it clears a **cache whose entire purpose is to persist**; `mono_cache_find` exists to avoid regenerating instances. Resetting it per-instantiation would defeat it, and nothing outside `type_erasure.spl` imports the module |
| `alloc_inference_reset` | deleted | **redundant even if called** — `alloc_inference_analyze()` already reinitializes all six vars itself (clears `ai_direct_alloc`/`ai_alloc_result`, reassigns `ai_fn_names`/`ai_fn_count`/`ai_fn_index` from `ceu_get_*`, reassigns `ai_callees`) |
| `bootstrap_fn_ret_types_reset` | deleted | **zero call sites by explicit design**, per an in-tree note at `bootstrap_globals.spl`: the registry must accumulate across ALL closure modules because cross-module call sites need the callee module's declared types, and the native-build worker is one process per build. Calling it would have *broken* cross-module lowering |

#### Both hazards from the env-mirror fix were checked, per reset

**(a) Reader consults a different source first (fix present-but-inert).** Only
`bootstrap_fn_ret_types_reset` has this shape, and it is decisive against
wiring it: the reader at `_MirLoweringExpr/switch_operators_calls.spl` consults
the **HIR symbol table first** (`self.symbols.get_symbol_raw(...)` →
`HirTypeKind.Function(_, ret, _)`) and only falls through to
`bootstrap_fn_ret_type_lookup` afterwards, with two further fallbacks below
that. Registration is also **`Str`-returns only**. So a reset there would have
been inert for every case the symbol table answers — exactly the
present-and-inert failure the env-mirror fix had to avoid.

**(b) `*_count_set(0)` erasing a high-water mark.** None of the four has this
hazard: `alloc_inference_reset`'s `ai_fn_count = 0` and `intern_reset`'s
`intern_count = 0` were each paired with clearing every backing array, so no
stale tail could survive. (The sibling that *is* called,
`bootstrap_mir_functions_reset`, does zero a count — but likewise clears all
seven parallel arrays alongside it.)

A design note recording why `_bootstrap_fn_ret_types` has no reset was added at
its declaration in `mir_data.spl`, so the affordance is not re-added by a later
lane reading the same "missing reset" signal.

Sibling resets that *are* wired, for reference: `type_subst_reset`
(`type_erasure.spl`, per-instantiation), `ceu_reset` (`alloc_inference.spl`,
per-run), `bootstrap_mir_functions_reset` (`bootstrap_globals.spl`, per-build
and per-module).

### Sibling: `ast_reset()` inside a live transient array scope — ENUMERATED, NOT FIXED

Two sites run `ast_reset()` *before* `rt_transient_array_scope_end()`:

- `src/compiler/80.driver/driver_source_pipeline_parsing.spl` —
  `driver_end_transient_parse_scope()`
- `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` —
  `parse_and_build_module_scoped()`

`ast_reset()` does not only `.clear()`; it re-seeds arenas by assignment
(`ast_module_decl_slots_clear()` does `module_decl_slots = []`, and the
nil-guards in `expr_reset`/`stmt_reset` allocate fresh backing arrays). Those
fresh allocations land in the scope that is about to be torn down — "reset inside
a dying scope is allocation into a grave".

**The naive fix (move `ast_reset()` after `scope_end`) was tried and REVERTED.**
It is not obviously an improvement: the arenas *grew* during the parse, and that
growth reallocated inside the scope, so after `scope_end` the globals hold freed
handles either way. Resetting before `scope_end` allocates into dying memory;
resetting after `scope_end` `.clear()`s freed memory. The second may be worse.

A correct fix has to re-materialize the arenas outside the scope after teardown
(what `driver_prepare_transient_parse_scope()` already does for the *next*
cycle), not merely reorder two statements. Landing the reorder without a runtime
reproduction would be trading a quiet defect for a possibly louder one on a
memory-corruption-sensitive path, so it is recorded here instead. **No runtime
reproduction of harm from this site was obtained** — the next cycle's
`driver_prepare_transient_parse_scope()` overwrites the dangling handles before
any read, which may be why it has stayed latent.
