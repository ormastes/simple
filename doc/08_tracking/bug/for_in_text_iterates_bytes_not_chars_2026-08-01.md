# `for ch in <text>` iterates BYTES, not characters (2026-08-01)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
corrected earlier by inspection. Native AOT is UNVERIFIED — see "Native AOT lane
is unmeasurable" below; it shares the fixed MIR lowering site.

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

| Engine | Site | Before | After (2026-08-01) |
|---|---|---|---|
| pure-Simple MIR | `src/compiler/50.mir/mir_lowering_stmts.spl:1988-2004` | **already correct** — emits `rt_string_chars` | unchanged; not executable today |
| pure-Simple AST interpreter | `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:471` | **BUG** — `substring(i, i+1)` stepped over `len()` (byte length) | fixed by inspection (commit `872138917991`); still not executable |
| Rust seed AST interpreter | `interpreter_helpers/collections.rs:403`, `interpreter_call/block_execution.rs:149` | correct (Rust `.chars()`) | unchanged |
| **Rust seed MIR/JIT** | `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` (`HirStmt::For`) | **BUG** — `rt_for_iterable` + `rt_array_len` + `IndexGet`; no string case | **FIXED and MEASURED GREEN** — normalizes with `rt_string_chars` when the iterable's `HirType` is `String` (or `Struct` named `String`/`text`/`str`) |
| Rust seed native AOT | same MIR site as above | **BUG** (same lowering) | **fix applied, but UNVERIFIED** — the `--native` emit path is dead on this build (live control fails, see below) |
| runtime `rt_for_iterable` | `src/runtime/runtime_native.c:5583`, `src/runtime/simple_core/core_array.spl:388` | **BUG** — dicts converted, strings passed through to byte indexing | backstop left as-is; it still cannot fire for unregistered string handles, which is exactly why the fix had to move to the lowering site |

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

## CLOSED on the seed JIT/MIR lane (2026-08-01) — option (a) taken

`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`, `HirStmt::For`: the
iterable normalization now selects the runtime helper by static type —
`rt_string_chars` for text, `rt_for_iterable` for everything else. The existing
counted `rt_array_len` / `IndexGet` loop is correct unchanged, because
`rt_string_chars` returns an array of 1-codepoint texts.

Option (b) (making the seed string representation visible to `rt_core_as_string`)
was NOT taken: it changes a runtime-wide invariant to fix one call site.

Text detection mirrors the existing idiom at `lowering_expr_call.rs:247` —
`HirType::String`, or `HirType::Struct` named `String`/`text`/`str`.

### Measured, seed rebuilt with `cargo build --profile bootstrap --features llvm`
(binary 154,459,120 B — canonical WITH-LLVM size, not the 32 MB no-LLVM build)

`simple run` (JIT/MIR), probe carries a deliberately-failing SENTINEL row:

```
                          BEFORE                    AFTER
for_in_text_iters         FAIL got=6 want=5         PASS got=5
for_in_text_acc_len       FAIL got=-1 want=6        PASS got=6
for_in_chars_iters        PASS got=5                PASS got=5
for_in_chars_acc_len      PASS got=6                PASS got=6
for_in_ascii_iters        PASS got=3                PASS got=3
for_in_ascii_acc_len      PASS got=3                PASS got=3
SENTINEL_must_fail        FAIL got=1 want=2         FAIL got=1 want=2
```

The SENTINEL still fails after the fix, so the green rows are not a harness
that stopped asserting. Note the ASCII rows PASS even when the bug is present
(bytes == chars for ASCII) — they are a regression guard, **not** diagnostic.

Regression probe (same falsifiable shape) confirms the non-text paths still
route through `rt_for_iterable`:

```
PASS for_in_int_array got=60
PASS for_in_str_array_len got=4      (for s in ["ab","cd"] — array of str, not str)
PASS for_in_dict_pairs got=2         (dict->tuple conversion still fires)
FAIL SENTINEL_must_fail got=7 want=8
```

## Native AOT lane: original claim CORRECTED (2026-08-01)

This section previously claimed the `--native` emit path was broken outright,
citing a 3768-byte stripped ELF that ran, printed nothing and exited 0 "including
for a trivial `fn main(): print("HELLO_CONTROL")`". **That scope was wrong.**
Root-caused and corrected in
`doc/08_tracking/bug/native_emit_silent_empty_binary_2026-08-01.md`. Summary:

- On the **canonical Rust bootstrap seed**
  (`src/compiler_rust/target/bootstrap/simple`, 154 MB with LLVM), the
  hello-world control **PASSES**: a 2.6 MB binary that prints and exits 0.
  Verified across both flag orders, absolute paths inside and outside the repo,
  `--backend=cranelift`, `--opt-level none`, and both `native-build` forms.
- The real defect was confined to the **compiled pure-Simple CLI lane**
  (`src/app/cli/bootstrap_main.spl`): the enum `options.mode` did not survive
  struct transport into the driver, `compile()` fell through with no mode
  matched, and returned Success having emitted nothing while exiting 0. Fixed at
  origin `e1150d003b7c4e39f170ce40626b7155e087faa6` via `options.cli_mode_text =
  "aot"`, plus a positive-artifact assertion so it can never be silent again.
- `nm -g` reporting no symbols was a **red herring** — host `--native` output is
  auto-stripped by default, so working binaries look identical.
- The **absolute-path trap did not fire** here; absolute paths compiled and ran
  correctly. Disregard the earlier note in this section that claimed otherwise.

**Still unproven:** the claim that this for-in defect "reproduced identically on
the native AOT path". Native AOT shares the MIR lowering site that was fixed, so
it is expected to be corrected too — but that remains inference, not
measurement. Re-measure on the canonical seed, asserting a positive artifact
(non-trivial size + expected stdout from a live control), not exit 0.

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
