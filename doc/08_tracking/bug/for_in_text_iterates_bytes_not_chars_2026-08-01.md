# `for ch in <text>` iterates BYTES, not characters (2026-08-01)

Status: PARTIALLY FIXED — pure-Simple lane corrected; **Rust seed JIT/native lane still RED**.

Related:
- `doc/08_tracking/bug/char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30.md`
  (carries the criteria for which `char_code_at` call sites are safe to migrate)
- `doc/08_tracking/bug/2026-08-01_interpreter_char_code_at_byte_indexed.md`
- `doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`
- `doc/08_tracking/bug/divergence_byte_char_find_option_sweep_2026-08-01.md`

## Symptom

`"café,"` is 6 bytes / 5 codepoints.

```
for ch in s:          # runs 6 times; accumulator ends EMPTY, acc.len() == -1
for ch in s.chars():  # runs 5 times; accumulator == "café,"  (correct)
```

The bound value is not a 1-char text — it is a raw byte read through the array
index path, so `acc = acc + ch` produces a corrupt text whose `len()` is `-1`
and which prints as nothing.

## Engine measured

**Rust seed, JIT/MIR path** — `src/compiler_rust/target/bootstrap/simple run`.
Reproduced identically on the **native AOT** path
(`... compile <f> --native`). `SIMPLE_NO_JIT=1` and `SIMPLE_INTERPRET=1` did
not change the result on this build (they did not select the Rust AST
interpreter). `bin/simple` has no `run`/`test`/`lint` subcommand, so the
self-hosted binary could not be used to execute anything.

Probe (self-checking, carries a deliberately-failing SENTINEL row so a silent
pass is impossible):
`/tmp/.../scratchpad/forch/probe3.spl`, direct-seam probe `probe4.spl`.

Observed:

```
FAIL for_in_text_iters    got=6 want=5
FAIL for_in_text_acc_len  got=-1 want=6
PASS for_in_chars_iters   got=5
PASS for_in_chars_acc_len got=6
FAIL SENTINEL_must_fail   got=1 want=2     <- probe proven falsifiable
```

## Root cause — five independent engines, NOT one lowering site

The originally-proposed fix ("lower `for v in <text>` to `for v in <text>.chars()`
at the single lowering site") is **the wrong shape**:

1. There is no single lowering site. Each engine decides string iteration itself.
2. A `.chars()` rewrite would be **undone**: `src/compiler/10.frontend/desugar/collection_desugar.spl:259-286`
   (Pattern F) rewrites `for x in s.chars()` → `for x in s`, the exact opposite
   direction.

Per-engine state:

| Engine | Site | Before |
|---|---|---|
| pure-Simple MIR | `src/compiler/50.mir/mir_lowering_stmts.spl:1988-2004` | **already correct** — emits `rt_string_chars` |
| pure-Simple AST interpreter | `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:471` | **BUG** — `substring(i, i+1)` stepped over `len()` (byte length) |
| Rust seed AST interpreter | `interpreter_helpers/collections.rs:403`, `interpreter_call/block_execution.rs:149` | correct (Rust `.chars()`) |
| Rust seed MIR/JIT + native AOT | `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:1388` | **BUG** — `rt_for_iterable` + `rt_array_len` + `IndexGet`; no string case |
| runtime `rt_for_iterable` | `src/runtime/runtime_native.c:5583`, `src/runtime/simple_core/core_array.spl:388` | **BUG** — dicts converted, strings passed through to byte indexing |

The real seam for the index-based for-loop path is **`rt_for_iterable`**, not a
`.chars()` desugar.

## Fixed in this change

- `src/compiler/10.frontend/core/interpreter/eval_stmts.spl` — text branch now
  iterates `str_val.chars()` by char index instead of byte-stepping
  `substring(i, i+1)`. Bound to a `val` first so Pattern F cannot rewrite it
  back into the byte-indexed shape.
- `src/runtime/simple_core/core_array.spl` — `rt_for_iterable` converts text to
  its codepoint array (backstop for statically-erased text, which bypasses the
  `local_is_str` guard in MIR lowering).
- `src/runtime/simple_core/core_string.spl` — new `rt_string_is_text` predicate
  (`pub`, so split core files can decode the kind without duplicating it).
- `src/runtime/runtime_native.c` — mirror of the `core_array.spl` change; the
  file already documents that the two `rt_for_iterable` impls must stay in sync.

**Verification status: BY INSPECTION ONLY.** None of these four is proven by
execution:
- The `.spl` interpreter and MIR lane cannot be executed today — `bin/simple`
  has no `run`/`test`, and `simple test` silently delegates to the Rust seed
  child, so a green suite is never evidence for the pure-Simple lane.
- The `runtime_native.c` change did **not** flip the probe. `rt_core_as_string`
  requires string-registry membership (`rt_core_is_registered_string`), and the
  string handles reaching `rt_for_iterable` on the seed JIT / native AOT paths
  are not registered core strings — so the new branch is not taken there. The
  change is still correct for registered-core-string callers, but it does not
  close the measured defect.

## STILL OPEN

**The Rust seed JIT/MIR + native AOT path remains broken.** This is the engine
everyone actually hits via `simple run` / `--native`. Closing it needs either:

(a) a string case in `lowering_stmt.rs:1388` (emit `rt_string_chars` before the
    `rt_array_len`/`IndexGet` loop, mirroring `mir_lowering_stmts.spl:1988`), or
(b) making the seed/native string representation visible to
    `rt_core_as_string` so the `rt_for_iterable` backstop actually fires.

(a) is the direct analogue of the already-correct pure-Simple lowering and is
the recommended fix. It is Rust and bootstrap-only, which is why it was not
taken here.

## Blast radius (measured, owned source only)

- `for X in <expr>.chars()`: **84** sites — **unaffected**. These already
  iterate codepoints on every engine; none of the changes touch them.
- `for X in "<string literal>"`: **1** site.
- `char_code_at` call sites: **443** (superset of the ~120 sitting inside
  `while i < s.len(): s.char_code_at(i)` loops that over-run on non-ASCII).

Direct `for ch in <text>` is rare in owned source *because* callers were pushed
onto the `char_code_at` idiom by this defect. No caller can have meaningfully
"adapted to the byte behaviour": the engines **disagree with each other**
(pure-Simple MIR and both Rust AST interpreters already yield codepoints), so
there was never a consistent byte semantics to depend on. The change is
therefore corrective, and the before/after difference is confined to text
iterables on the two engines that were wrong.

## Explicitly NOT done

The ~120 `char_code_at` while-loops were **not** migrated. That is cleanup for a
later pass, gated on the safety criteria in
`char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30.md`, and it
should not start until the Rust seed JIT/native lane above is closed — otherwise
migrated callers would regress on the engine most people run.
