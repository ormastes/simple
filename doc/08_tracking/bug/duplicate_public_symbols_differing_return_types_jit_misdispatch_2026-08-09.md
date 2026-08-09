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

## Recommended approach

1. Decide whether `src/app/io/**` and `src/lib/nogc_sync_mut/io/**` should both
   exist. That is the root cause; everything else is downstream.
2. Fix **Class B (identical-signature)** first — it is the one that silently
   produces wrong answers and can vacate specs.
3. Use the 373 count as the regression metric. Absence of a specific warning is
   the bar for a single symbol; a falling total is the bar for the campaign.
