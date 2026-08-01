# Bug: bootstrap AST env mirror serves stale nodes and bypasses the stale-index guard

**ID:** ast_env_mirror_bypasses_stale_index_guard_2026-08-01
**Severity:** P2 — latent correctness (silent wrong AST tag) + proven O(N^2) + proven exec ceiling
**Status:** Diagnosed, NOT fixed. Fix proposed below; deliberately not landed (see "Why not fixed yet")
**Reported:** 2026-08-01
**Mode:** only when `SIMPLE_BOOTSTRAP=1` and `SIMPLE_NATIVE_ARENA_DECLS != 1`
**Related:** `ast_env_var_quadratic_parse_2026-06-13.md` (perf only),
`flat_bridge_type_index_across_ast_reset_2026-07-12.md` (the guard this defeats),
`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`

---

## Mechanism (PROVED by reading the code)

Under bootstrap mode the stmt/expr arenas keep a **mirror** of every node field in
real process environment variables, keyed
`SIMPLE_BOOTSTRAP_EXPR_<idx>_<FIELD>` / `SIMPLE_BOOTSTRAP_STMT_<idx>_<FIELD>`.

- Gate: `expr_env_mirror_enabled()` — `_AstExpr/nodes.spl:167`; `stmt_env_mirror_enabled()` — `ast_stmt.spl:105`.
  Memoized in `expr_env_mirror_slot` / `stmt_env_mirror_slot`; an empty slot falls back to a live env read.
- Writers: `expr_i64_set` / `expr_text_set` / `expr_list_set` (`nodes.spl:214+`) — no-ops unless the mirror is enabled.
- `expr_alloc` (`nodes.spl:414`) writes **all 11 fields** to both the arrays and the mirror.
- Readers are **env-first, array-fallback**: `expr_get_tag` / `_span` / `_int` / `_str` /
  `_left` / `_right` / `_extra` / `_args` / `_arg_names` / `_stmts` — `_AstExpr/accessors.spl:91-176`.

The mirror is **not** the sole store. `expr_tag`, `expr_left`, ... are written unconditionally,
so the mirror is redundant duplication, not the backing store. That is why the finding lane could
not prove a defect: for any live index the two stores agree.

### The actual defect: reset clears the arrays but never unsets the env

`expr_reset()` (`nodes.spl:341-412`) clears every array and calls `expr_count_set(0)`.
It **never unsets a single `SIMPLE_BOOTSTRAP_EXPR_<idx>_<FIELD>` entry**, and there is no
`rt_env_unset` anywhere in the AST layer. Indices below the new file's node count get
overwritten by the next `expr_alloc`; **indices above it retain the previous file's values.**

`expr_get_tag` reads the env **before** its bounds guard:

```
fn expr_get_tag(idx: i64) -> i64:
    val direct = expr_env_read(idx, "TAG")
    if direct != "":
        ... return parsed          # <-- returns here
    if idx < 0 or idx >= expr_owner_len():
        print "[expr_get_tag] OOB ..."     # <-- unreachable when the mirror answered
        return -1
```

That guard was added specifically for
`flat_bridge_type_index_across_ast_reset_2026-07-12.md` ("index is 48 but length is 13",
which was killing the stage-4 build). **Under the mirror it is unreachable**: a stale index
captured before an `ast_reset` is answered out of the previous compilation unit's env entry and
returned as a valid tag — silently wrong — instead of tripping the -1 sentinel and its diagnostic.
The generation diagnostics added in `5eef43f775e` (lane L6) are bypassed the same way.

So the mirror does not merely duplicate state: **it cross-contaminates compilation units within one
process and disables the guard for exactly the mode that needs it.** This is the defect class the
sibling audit was chasing.

## Measured consequences

Native C probe modelling libc `setenv`/`getenv` at 11 entries per expr node (host glibc,
`ARG_MAX = 2097152`). This lane measures the *store*, not the Simple compiler.

| expr nodes | environ entries | batch `setenv` time |
|-----------|-----------------|---------------------|
| 250       | 2,750           | 0.030 s |
| 500       | 5,500           | 0.061 s |
| 1,000     | 11,000          | 0.263 s |
| 2,000     | 22,000          | 0.985 s |

~4x per doubling => **O(N^2) confirmed**. A single `getenv` at 22,000 entries costs ~160 us
(20,000 lookups = 3.195 s) — and that is paid on *every field read* of the env-first accessors.

**Exec ceiling — PROVED.** With 512-byte field values, `fork`+`execl` began failing with
`E2BIG` at **~4,000 expr nodes / 2,163,431 env bytes**. With typical short values (~40 bytes/entry)
the same 2 MB `ARG_MAX` is reached at roughly 4,700 expr nodes. Past that point *every child
process exec fails*, including the linker (`mold`/`lld`/`ld`, `70.backend/linker/`).

Scope bound (important, and it limits the blast radius): because indices restart at 0 each file
and overwrite existing keys, environ size is bounded by the **largest single file's** node count,
not the total across the build. Whether any single repo source file exceeds ~4,700 expr nodes is
**UNMEASURED** — I could not run the bootstrap compiler this session (see below).

## Is the enabling condition still live? YES — this is why it must not simply be deleted

`ast_decl_arena_default()` (`_Ast/decl_nodes.spl:136`) documents the reason, and it still holds:

> under a tree-walk interpreter, module-level arrays may not persist between calls, and the env
> store is the reliable store there

The **decl** arena was already migrated to arena-preferred-by-default on 2026-07-24, but it
deliberately kept `SIMPLE_BOOTSTRAP=1` on the legacy env path for that reason. The stmt/expr
siblings were never given the equivalent opt-out and have no default-flip at all. Live
mirror-enabled lane today: `src/app/ci/build_simpleos_toolchain.spl:402` runs
`SIMPLE_BOOTSTRAP=1 ... native-build --source src/compiler --source src/lib --source src/app`
with no `SIMPLE_NATIVE_ARENA_DECLS=1`.

**Do not "fix" this by deleting the fallback or the env read.** The fail-safe is load-bearing.

## Proposed fix (conservative, keeps the fallback)

Bound the env-first read by the live node count rather than reordering the guard:

```
fn expr_env_read(idx: i64, field: text) -> text:
    if not expr_env_mirror_enabled():
        return ""
    if idx < 0 or idx >= expr_count_env():   # NEW: stale//OOB index is not a live node
        return ""
    rt_env_get(expr_key(idx, field)) ?? ""
```

`expr_count_env()` is env-authoritative under the mirror (`expr_reset` writes COUNT=0, `expr_alloc`
bumps it before writing fields), so this refuses only indices that provably are not live nodes,
and it restores reachability of the `expr_get_tag` OOB guard. Same change for `stmt_env_read`.

## Why not fixed yet

The guard depends on `expr_count_env()` being trustworthy in the one environment where module-level
state is known to be unreliable. If `SIMPLE_BOOTSTRAP_EXPR_COUNT` is ever absent while the
per-index entries are present, `expr_count_env()` returns 0 and the proposed guard would reject
**every** env read — turning a latent bug into a total bootstrap failure. That is the same
fail-safe reasoning that kept this code as it is.

Validating the change requires running the bootstrap interpreter lane, which was not possible this
session: the live `bin/simple` has no `run`/`test` subcommands and `bin/simple_seed` predates
several parser fixes. **This must be landed only together with a bootstrap-lane run that exercises
`SIMPLE_BOOTSTRAP=1` across a multi-file parse.**

## Repro sketch (not yet executed)

Under `SIMPLE_BOOTSTRAP=1` without `SIMPLE_NATIVE_ARENA_DECLS=1`, parse a large file (N expr nodes),
then parse a small one, then read a node index between the two counts: `expr_get_tag` returns the
first file's tag instead of -1. Expected after fix: -1 plus the OOB diagnostic.
