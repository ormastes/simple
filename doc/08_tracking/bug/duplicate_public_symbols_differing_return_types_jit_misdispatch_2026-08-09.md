# Co-compiled symbol collisions — 373 in a single spec run, two distinct failure classes

**Date:** 2026-08-09 (rewritten same day after measurement disproved the first version)
**Status:** OPEN — systemic, far larger than first believed. A targeted fix was attempted, MEASURED, and did not work.
**Severity:** silent wrong-body dispatch; the same-signature class can make importing specs **vacuous**

## Measured scale

A single run of `test/01_unit/compiler/cache/action_key_spec.spl` from the main
repo emits **373** `compiler_cross_module_private_symbol_collision` warnings.
The original framing of this bug as "three symbols" was wrong by two orders of
magnitude.

## TWO distinct failure classes — the second is worse

### Class A — differing signatures (ambiguity fallback)

```
public function `file_read_bytes` has 3 co-compiled definitions with 2 differing
signatures ((text)->[i64] vs (text)->[u8]); JIT call sites resolve by exact
arg-type match (mangled `$dupN` variants), falling back to the last definition
when types are ambiguous — a fallback hit may still dispatch to the wrong one.
```

Bad, but at least a type/arity error can fire in some configurations.

### Class B — IDENTICAL signatures (silent win, spec-vacuating)

```
private helper `_file_shell` has 2 co-compiled definitions across 2 modules with
the SAME signature ((text)->Tuple([text, text, i64])) — one silently wins and the
rest are discarded. Because the signatures agree, no type/arity error and no
ambiguity fallback can fire, so a call resolves to a different module's body than
the one it imported: a silent wrong answer, and the shape that makes an
importing spec vacuous.
```

**This is the dangerous class.** No diagnostic can fire, and a spec that imports
module X may be exercising module Y's body. Affected symbols observed include
`_file_shell`, `_file_shell_bool`, `_file_shell_int`, `_file_shell_output`,
`_shell_command_args`, `shell_bool`, `shell_int`, `shell_lines`, `shell_output`,
`shell_output_default`, `shell_output_trimmed` — a whole `io`/`process_ops`
family duplicated across `src/app/io/**` and `src/lib/nogc_sync_mut/io/**`.

## Attempted fix — MEASURED, did not work

Three branches converged what looked like the live pairs:

- `shell` → `ProcessResult` (superset of `ShellResult`; zero call sites needed changing)
- `dir_remove_all` → `bool` (the `i32` was `if rt_dir_remove_all(p): 0 else: -1`
  over the SAME bool — **not** an errno, so the `Result` convergence recommended
  in this doc's first version would have been pure ceremony)
- `file_read_bytes` → removed 3 provably-dead definitions (two identical
  hardcoded mocks returning `Some([72,101,108,108,111])`)

Applied to the main repo and re-measured. Result **after** the fix:

| symbol | before | after |
|---|---|---|
| `dir_remove_all` | 2 defs, `bool` vs `i32` | **3** defs, `bool` vs `i64` |
| `file_read_bytes` | 2 defs | **3** defs, plus a second separate group |
| `shell` | 2 defs, `ProcessResult` vs `ShellResult` | **4** defs, `ProcessResult` vs `Tuple([text,text,i64])` |

The collisions did not clear. There are more definitions than any single-symbol
analysis found, including `Tuple`-returning variants in `src/app/io/**` that no
agent had identified. The changes were **reverted**; the work is retained on
branches `worktree-agent-acd59b64711418ca3`, `-ae00152ca79d4e0dd`,
`-a7bcfd7de59c82b0a` for whoever takes the systemic fix.

## Why per-symbol fixes fail here

`src/app/io/**` and `src/lib/nogc_sync_mut/io/**` appear to be **parallel
implementations of the same io surface**, co-compiled into one program. Fixing
one symbol at a time cannot converge that; each fix reveals another definition
in the other tree. This needs a decision about the two trees, not a rename.

## Verification note — you cannot measure this from a worktree

`use std.X` resolves unconditionally to `/home/ormastes/dev/pub/simple/src/lib/`,
never a worktree copy. A worktree agent editing `src/lib/**` sees its change do
nothing. Measure from the main repo root only:

```
SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 bin/simple test <any spec> 2>&1 \
  | grep -c co-compiled
```

`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1` prints the OWNER PATH of each colliding
definition, which is what makes the two-parallel-trees structure visible.

## CRITICAL: converging signatures makes things WORSE, not better

Measured 2026-08-09, second attempt. An agent converged every `file_read_bytes`
definition onto `[u8]` — the obviously "correct" canonical type. Result:

```
BEFORE: file_read_bytes, 2 defs, DIFFERING signatures ((text)->[i64] vs (text)->[u8])   [Class A]
AFTER:  file_read_bytes, 3 defs, IDENTICAL signature   ((text)->[u8])                    [Class B]
        Defined in: .../io/file_ops.spl, .../io_runtime.spl, .../sffi/io.spl
```

**It converted a Class A collision into a Class B collision — the worse class.**

With differing signatures, exact-arg-type match can still pick correctly in many
call sites, and a type error can fire. With identical signatures, one definition
silently wins, **no diagnostic can ever fire**, and importing specs may exercise
a different module's body.

So the intuitive fix — "make the signatures agree" — is actively harmful on its
own. Signature convergence is only safe when combined with **deleting the
duplicate definitions**, leaving exactly one. Renaming is likewise only safe if
the result is one definition per name.

The change was reverted. Total collisions during that attempt read 431 vs the
375 baseline, though other sessions' concurrent edits were also present in the
working copy, so that delta is not solely attributable.

**Rule for anyone continuing this work:** the metric is the count of
DEFINITIONS per symbol, driven to one. Signature agreement is not the goal and
optimising for it makes the codebase less diagnosable.

## 2026-08-10 — first verified reduction landed: mod_stub facade dedup

Mechanism confirmed: this is the SAME root cause as
`duplicate_hirtype_enum_decls_drop_module_to_interpreter_2026-08-04.md` /
`duplicate_struct_decls_shadow_field_types_2026-08-10.md` (seed JIT registers
declarations by BARE NAME; commit `1d68beb0dca` deduped struct decls), applied
to functions. The struct fix was "delete/rename to one definition per bare
name" — exactly the metric this doc already mandates for functions.

Largest single contributor measured: `src/lib/nogc_sync_mut/io/mod_stub.spl`
appeared in **56 of 357** collision warnings (baseline re-measured 2026-08-10
via `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 bin/simple test
test/01_unit/compiler/cache/action_key_spec.spl`). It locally DEFINED ~50
duplicate-named fns: error-print `cli_*` stubs (Class B vs the real
`src/app/io/**` handlers and `src/lib/nogc_sync_mut/sffi/cli.spl` — if a stub
silently wins, subcommands print "requires Rust SFFI", i.e. the historical
"bin/simple lost all subcommands" shape) plus thin extern wrappers duplicating
`dir_ops`/`env_ops`/`process_ops`. Zero importers of any of those names via
mod_stub except `is_dir` (2 call sites).

Fix applied (safe under this doc's rule — it DELETES definitions, converging
nothing): mod_stub is now a pure `export use` facade over the canonical owners
(file_ops/dir_ops/env_ops/process_ops), mirroring the conversion already done
in `src/lib/gc_async_mut/io/mod_stub.spl`. Measured: 357 → **345** warnings,
and mod_stub appears in **0** of them (56 → 0); many 2-def groups (cli_compile,
cli_constr, cli_gen_lean, all cli_run_*) are now 1-def. action_key_spec still
32/32 green; re-export surface probed live (`is_dir`/`cwd`/`file_exists`).
Regression guard: `test/01_unit/lib/io/mod_stub_no_duplicate_definitions_spec.spl`
(sabotage-verified: re-adding a local fn turns it red).

What the remaining "tree-consolidation decision" actually is (still OPEN):
- `src/app/io/{cli_ops,process_ops,context_ops,_CliCommands/**}` vs
  `src/lib/nogc_sync_mut/{io/**, sffi/{cli,io}.spl, io_runtime.spl}` — the
  cli_*/process_*/dir_* surface still has 2 live definition families (real app
  handlers vs real SFFI wrappers, both with importers; neither is deletable
  without choosing an owner for the CLI surface — app-owner call).
- Other parallel pairs unrelated to io: `nogc_sync_mut/path.spl` vs
  `nogc_async_mut/path.spl` (28+28 warnings), `common/binary_io.spl` vs
  `nogc_async_mut/binary_io.spl` (17+17), `nogc_sync_mut/cuda/mod.spl` vs
  `gc_async_mut/cuda/__init__.spl` (21+21), fix-rule impls (20+16). These are
  the stdlib-tier families duplicated across memory tiers — consolidating them
  is a stdlib-tier architecture decision, not a rename.

## Recommended approach

1. Decide whether `src/app/io/**` and `src/lib/nogc_sync_mut/io/**` should both
   exist. That is the root cause; everything else is downstream.
2. Fix **Class B (identical-signature)** first — it is the one that silently
   produces wrong answers and can vacate specs.
3. Use the 373 count as the regression metric. Absence of a specific warning is
   the bar for a single symbol; a falling total is the bar for the campaign.
