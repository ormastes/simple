# Bug: bootstrap AST env mirror serves stale nodes and bypasses the stale-index guard

**ID:** ast_env_mirror_bypasses_stale_index_guard_2026-08-01
**Severity:** P1 — latent correctness (silent wrong AST tag) + proven O(N^2) + **exec ceiling already exceeded by current source files** (measured 2026-08-01)
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
(E2BIG, stale cross-unit reads, O(N^2)) close together. The premise that kept the mirror alive —
"under a tree-walk interpreter, module-level arrays may not persist between calls" — was tested
directly and **DISPROVED**; see "Decisive experiment" below. The decl-side env store is a separate
mechanism and is **unchanged**.
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
not the total across the build. That reduced the open question to a single maximum — **now measured
below.**

## Largest-file measurement — the ceiling is ALREADY EXCEEDED (2026-08-01)

**Answer: yes, and not marginally.** The `~4,700 expr node` exec ceiling is not a future risk to
guard against; current sources are several times past it. **Headroom is negative.**

### Instrument (exact, and why it is exact)

`expr_alloc` (`nodes.spl:414`) increments `expr_count_slot[0]` via `expr_count_set` **before and
independently of** any env mirroring — the mirror writes (`expr_i64_set` etc.) are separately gated
on `expr_env_mirror_enabled()`. So parsing with `SIMPLE_BOOTSTRAP` **unset** and reading
`expr_count_env()` yields the identical node count the bootstrap mirror would have produced, without
paying the O(N^2) `setenv` cost. The counts below are that counter — not a source-line proxy.

- Driver: `parse_module_silent_checked(content, path)` then `expr_count_env()`, one file per
  iteration (`parse_module` resets the arena per file, matching the real per-file scope bound).
- Binary: `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731` (Jul 30, 154 MB).
- **Lane: interpreter.** The JIT cannot resolve `parse_module_silent_checked` and drops the whole
  module to the interpreter. The parser actually executing is the in-tree Simple source under
  `src/compiler/10.frontend/`, which is exactly the layer that owns the mirror.
- Corpus: 39,730 `.spl` files, deduplicated by `readlink -f` so the ~17 `src/compiler` layer
  symlinks are not double-counted.

### Exact counts (PROVED — parser arena counter)

| file | bytes | expr nodes | nodes/byte |
|------|-------|-----------|-----------|
| `test/unit/lib/nogc_async_mut/steam/controller_hid_spec.spl` | 2,000 | **158** | 0.079 |
| `test/01_unit/nvfs/.spipe_matchers_nvfs_remount_persistence_spec.spl` | 4,000 | **339** | 0.085 |
| `test/unit/lib/text/text_length_spec.spl` | 8,000 | **586** | 0.073 |
| `test/01_unit/lib/http/h3/h3_frame_round_trip_spec.spl` | 12,000 | **917** | 0.076 |
| `src/compiler_rust/lib/std/src/core/dsl.spl` | 15,998 | **443** | 0.028 |

Density is **not** uniform: expression-dense spec code runs ~0.08 nodes/byte, while
declaration-heavy code (`dsl.spl`, 32% comment/blank, many type signatures) runs ~0.028. So
4,700 nodes corresponds to anywhere from **~55 KB to ~170 KB** of source depending on file style.
670 `.spl` files exceed 30 KB; 164 exceed 60 KB; 25 exceed 170 KB.

### Repo-wide distribution (APPROXIMATION — read the error bar)

Exactly measuring all 39,730 files is infeasible in the interpreter lane (a 50 KB file takes
minutes). Every file was instead scored with a static **atom count** (identifier/number/operator
tokens, comments stripped), calibrated against the five exact measurements above:

    nodes / atoms = 0.782, 0.864, 0.691, 0.871, 0.317

**The spread is wide (0.32-0.87) and the low end is real, not noise:** atoms in type annotations
and declarations never become expression nodes, so the proxy *overestimates* declaration-heavy
files. Results are therefore reported across the whole range, worst case first:

| threshold | ratio 0.32 (worst observed) | ratio 0.82 (typical) |
|-----------|----------------------------|----------------------|
| >= 4,000 expr nodes (measured `E2BIG` point) | **22 files** | **168 files** |
| >= 4,700 expr nodes (short-value ceiling)    | **20 files** | **132 files** |

Largest file, `src/app/ui.web/html_css.spl` (52,651 atoms): **~17,000-43,000 expr nodes**, i.e.
**~3.6x to 9x the exec ceiling**. Even the most pessimistic calibration leaves it far over.
Top candidates by estimated nodes:

| file | atoms | ~nodes (0.32-0.82) |
|------|-------|--------------------|
| `src/app/ui.web/html_css.spl` | 52,651 | 16,800 - 43,200 |
| `src/app/office/sheets/formula.spl` | 49,736 | 15,900 - 40,800 |
| `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` | 40,765 | 13,000 - 33,400 |
| `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` | 39,061 | 12,500 - 32,000 |
| `src/lib/common/web/public_suffix_data.spl` | 28,056 | 9,000 - 23,000 |
| `src/compiler/70.backend/backend/llvm_native_link.spl` | 15,014 | 4,800 - 12,300 |

### A hard structural lower bound that needs no calibration at all

`src/lib/common/web/public_suffix_data.spl` contains **10,700 string literals**. Every string
literal is exactly one `expr_string_lit` -> one `expr_alloc`. That single file therefore allocates
**>= 10,700 expr nodes** — **2.3x the 4,700 ceiling and 2.7x the measured 4,000 `E2BIG` point** —
with no ratio, no proxy, and no extrapolation involved. **This alone settles the question**, and it
is why the wide calibration spread above does not change the verdict.

### The over-threshold files are inside the live mirror lane

`src/app/ci/build_simpleos_toolchain.spl:402` runs `SIMPLE_BOOTSTRAP=1 ... native-build --source
src/compiler --source src/lib --source src/app` with no `SIMPLE_NATIVE_ARENA_DECLS=1`. Of the files
over 4,700 nodes, **11 (worst-case ratio) to 64 (typical) are under `src/`**, and at both ends of
the range all four subtrees are represented — `src/lib`, `src/compiler`, `src/app`, `src/os`. So
every declared `--source` root contains at least one offender.

Caveat, stated honestly: that command also passes `--entry-closure --entry
src/app/simpleos_tool/main.spl`, so only modules reachable from that entry are actually parsed.
Which specific offenders land in the closure is **NOT measured here.**

### Consequence

Under the mirror, one such file drives environ past `ARG_MAX` (2,097,152 bytes) mid-parse, after
which **every subsequent `exec` fails with `E2BIG` — including the linker invocation** in
`70.backend/linker/`. The O(N^2) `setenv` cost at 10,000+ nodes is separately prohibitive (2,000
nodes already measured at ~1 s, growth ~4x per doubling; 10,700 nodes extrapolates to ~30 s of pure
`setenv` for that one file, before any `getenv` reads).

**This resolves the open question in the direction that removes a design decision rather than
adding one:** no guard threshold needs choosing, because current sources exceed every candidate
threshold — a size guard would fire on day one. The actionable consequences are (a) the mirror
cannot be enabled on this repo as-is, and (b) the proposed `expr_env_read` bounds-fix below must
**not** be validated by "the bootstrap lane still builds", because on a large file that lane cannot
build at all.

**Not measured / left open:** exact counts for files above ~16 KB (interpreter lane too slow this
session — the 3 largest files were still parsing when this was written), and the entry-closure
membership question above. Neither affects the verdict, which the 10,700-literal structural bound
establishes independently.


## Is the enabling condition still live? NO — DISPROVED 2026-08-01

An earlier revision of this document asserted the enabling condition still held and that the mirror
"must not simply be deleted". **That assertion was never tested. It has now been tested and it is
false.** The claim under test, from `ast_decl_arena_default()` (`_Ast/decl_nodes.spl:136`):

> under a tree-walk interpreter, module-level arrays may not persist between calls, and the env
> store is the reliable store there

### Decisive experiment (PROVED)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple_seed` (rebuilt 2026-08-01 from origin tip
`f93c9b2623`, contains all four parser fixes). **Lane: interpreter** (`SIMPLE_EXECUTION_MODE=interpret`)
— the mode the mirror exists to protect.

**1. Module-level arrays persist, in-module and cross-module.** A module-level `[i64]` written
through one function and read through another returns the written values; with the owner array in
module A and all access through A's exported accessors called from module B, unit A's 3 pushes read
back as 3 and a subsequent `clear()` + 1 push from unit B reads back as exactly 1 (`g0=21`, not
`11`). Identical under `interpret` and `jit`. Probes:
`/dev/shm` scratch, reproduced from the harness described below.

**2. The real parser, N=2 compilation units in one process, mirror ON vs OFF — arrays identical.**
Harness: `parse_module_silent_checked` on a generated 400-statement unit A, then a 2-line unit B,
then `expr_get_tag(len_b + 50)` — an index live in A and out of bounds in B.

| run | `owner_len` A | `owner_len` B | `expr_get_tag(51)` | verdict |
|-----|--------------|---------------|--------------------|---------|
| mirror OFF (`SIMPLE_BOOTSTRAP` unset) | 1200 | 1 | **-1** + OOB diagnostic | CLEAN |
| mirror ON (`SIMPLE_BOOTSTRAP=1`)      | 1200 | 1 | **1** (unit A's tag), no diagnostic | CONTAMINATED |
| **after retirement**, `SIMPLE_BOOTSTRAP=1` | 1200 | 1 | **-1** + OOB diagnostic | CLEAN |

The arena columns are **identical in all three rows**. The arrays persisted perfectly with the
mirror disabled, across two compilation units, in the interpreter, under `SIMPLE_BOOTSTRAP=1`.
The mirror contributed nothing to state retention — its only observable effect was the
contamination in row 2. This is the repro sketch that the previous revision left "not yet executed".

### Corroborating evidence already in-tree

`scripts/bootstrap/bootstrap-from-scratch.sh` pairs `SIMPLE_BOOTSTRAP=1` with
`SIMPLE_NATIVE_ARENA_DECLS=1` in `bootstrap_native_build_main` (line ~599) and in the stage3/stage4
arg sets (lines ~1224, ~1349). `expr_env_mirror_enabled()`/`stmt_env_mirror_enabled()` both already
tested `SIMPLE_NATIVE_ARENA_DECLS != 1`, so **the canonical self-host bootstrap was already running
with the expr/stmt mirror disabled.** Retirement does not create a new untested configuration; it
makes every lane take the configuration stage3/stage4 already proved. The lanes whose behaviour
actually changes are the ~30 SimpleOS/`scripts/os` lanes that set `SIMPLE_BOOTSTRAP=1` alone — and
per the measurement above those are the lanes already past `ARG_MAX` on real files, so removing the
mirror can only help them.

## Fix landed: the mirror is retired

The env mirror was **deleted**, not gated off — the repo rule is to remove unused code rather than
leave dead branches. The mechanism was fully contained in four files with **no external consumers**
(verified by symbol grep across `src/`):

| file | change |
|------|--------|
| `_AstExpr/nodes.spl` | mirror gate/slot, `expr_env_read`, `expr_mode_slots_refresh`, `expr_key`, the four `expr_*_set` writers, the three `expr_*_get` env readers, `env_value_nul_free`, and the now-dead `expr_parse_i64`/`expr_i64_list_join`/`expr_i64_list_split` removed; `expr_count_env`/`expr_count_set` now read/write `expr_count_slot[0]` only |
| `_AstExpr/accessors.spl` | all 11 env-first read prologues removed, so **the `expr_get_tag` bounds guard is now the first thing that runs** |
| `ast_stmt.spl` | same retirement on the stmt side, plus `stmt_is_if_val_decl` now reads `stmt_if_val_marker` unconditionally |
| `_Ast/decl_nodes.spl`, `_Ast/module_state.spl` | comments referencing the removed functions and the disproved premise corrected |

Deliberately **kept**: the `SIMPLE_TRACE_EXPR_TAGS` / `SIMPLE_TRACE_STMT_TAGS` trace prints and the
lane-L6 generation diagnostics (level-gated, default off — log-retention policy), and the entire
decl-side env store (`ast_decl_*`), which is a separate mechanism with its own live callers.

### The naive fix was correctly declined

The `expr_count_env()`-bounded `expr_env_read` proposed in the previous revision was **not** taken.
It trusts `SIMPLE_BOOTSTRAP_EXPR_COUNT` in the one environment where module state was believed
unreliable; had COUNT ever been absent it would have rejected every env read and converted a latent
bug into total bootstrap failure. Retirement removes the question instead of answering it.

### Verification performed

- Multi-unit A/B above (N=2 units in one process), interpreter lane — **the second unit is
  uncontaminated after the fix**, and the previously-unreachable OOB guard fires.
- Post-fix environ check: after parsing 1,200 expr nodes under `SIMPLE_BOOTSTRAP=1`,
  `SIMPLE_BOOTSTRAP_EXPR_0_TAG`, `..._500_TAG`, `..._EXPR_COUNT` and `SIMPLE_BOOTSTRAP_STMT_0_TAG`
  are all **empty** — zero mirror entries, so the `E2BIG` and O(N^2) mechanisms are gone by
  construction, not merely bounded.
- Corpus regression: **18 of 25** real `src/compiler/10.frontend/core/*.spl` files parsed in one
  process under `SIMPLE_BOOTSTRAP=1` — **0 failures**, and the 18 include all five files this change
  touches (`nodes.spl` 1355 nodes, `accessors.spl` 383, `ast_stmt.spl` 714, `decl_nodes.spl` 3389,
  `module_state.spl` 1545), i.e. the edited compiler parses itself. **Stated honestly: this run was
  truncated by a 1200 s harness timeout (interpreter lane is slow), not run to completion** — the
  remaining 7 files are unmeasured, and no `SUMMARY` line was emitted. It is a partial pass, not a
  clean sweep.

**Not verified in this lane (stated plainly):** a full stage3/stage4 bootstrap was not run here.
The risk is bounded by the corroborating evidence above — stage3/stage4 already set
`SIMPLE_NATIVE_ARENA_DECLS=1`, so those lanes were already exercising the exact code path this
change makes universal.
