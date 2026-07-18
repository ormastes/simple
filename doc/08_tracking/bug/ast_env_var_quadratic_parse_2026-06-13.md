# Bug: AST env-var backing store causes O(N²) parse time

**ID:** ast_env_var_quadratic_parse_2026-06-13  
**Severity:** P1 — `check` on 400+ top-level functions times out (>300 s)  
**Status:** Localized, fix proposed, not yet implemented  
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
