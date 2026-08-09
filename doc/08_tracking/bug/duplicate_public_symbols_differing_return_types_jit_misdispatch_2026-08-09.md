# Duplicate public symbols with differing return types — JIT may dispatch to the wrong one

**Date:** 2026-08-09
**Status:** OPEN — partial cleanup done, the actual hazard remains
**Severity:** silent wrong-value / wrong-type dispatch at runtime

## Symptom

Emitted by the compiler during an ordinary `bin/simple test` run:

```
warning: public function `dir_remove_all` has 2 co-compiled definitions with 2 differing
  signatures ((text)->bool vs (text)->i32); JIT call sites resolve by exact arg-type match
  (mangled `$dupN` variants), falling back to the last definition when types are ambiguous
  — a fallback hit may still dispatch to the wrong one.
  [compiler_cross_module_private_symbol_collision]
```

Three symbol families affected:

| symbol | signature A | signature B | callers |
|---|---|---|---|
| `dir_remove_all` | `(text)->bool` (`io_runtime.spl`) | `(text)->i32` (`io/dir_ops.spl`) | 40–175 per side |
| `shell` | `(text)->ProcessResult` (`process_ops.spl`) | `(text)->ShellResult` (`io_runtime.spl`) | 40–80 per side |
| `file_read_bytes` | `(text)->[i64]` | `(text)->[u8]` | dozens / 60+ |

## Why this matters

The two signatures in each pair return **incompatible types**. When the JIT cannot
resolve by exact argument type it falls back to the *last* definition — so a call
site can silently receive a `bool` where it expects an `i32`, or `[u8]` where it
expects `[i64]`. This is a wrong-value defect, not a compile error, and it will
surface as inexplicable downstream behaviour far from the call.

Note the argument types are IDENTICAL in every pair (`(text)`), which is exactly
the ambiguous case the warning says triggers last-definition fallback. This is
the worst configuration, not a benign one.

## What was done (2026-08-09)

Dead-by-name duplicates renamed and their call sites updated:

- `dir_remove_all` — 6 removed (`app_io_stub_*`, `nogc_sync_mut_io_stub_*`,
  `gc_async_mut_io_stub_*`, `nogc_async_mut_io_stub_*`, `ffi_*`, `sffi_*`).
  Co-compiled defs: 3 → 2.
- `shell` — 4 removed (`ffi_shell_exit_code`, `sffi_shell_exit_code`,
  `fileio_temp_shell_output`, `semihost_shell`). Co-compiled defs: 3 → 2.

12 edited files lint clean.

## What REMAINS — the actual hazard

**The cleanup removed noise, not the defect.** The original warning was already
about *2 definitions with differing signatures*; going 3 → 2 does not clear it.
All three live pairs above are still co-compiled with identical argument types
and incompatible return types.

`file_read_bytes` was not touched at all.

## Why it was not forced through

Each residual pair has 40–175 real callers spanning compiler, linker, GUI, and
QEMU code, reached via distinct import paths. A same-pass mechanical rename
across that surface is more likely to introduce a defect than remove one. The
agent was instructed to stop and report rather than force it, and did.

## Recommended fix

One dedicated task per symbol family, in this order (ascending caller count):

1. `file_read_bytes` — untouched, and the `[i64]`/`[u8]` split is the most
   likely to be a genuine porting artifact with one correct answer.
2. `shell` — decide whether `ProcessResult` and `ShellResult` are genuinely two
   concepts. If so both survive under distinct names; if not, converge them.
3. `dir_remove_all` — `bool` vs `i32` is probably a success-flag vs errno split;
   converge on `Result` rather than keeping either.

For each: identify callers per side FIRST (`/usr/bin/grep -rn`, not the wrapped
ugrep, which undercounts — measured 4 hits vs 17), then rename the non-canonical
side, then re-run and show the warning is GONE. Warning-count reduction is not
proof; absence of the warning is.
