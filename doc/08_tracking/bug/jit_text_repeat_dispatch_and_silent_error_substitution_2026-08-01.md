# JIT text-method dispatch gap silently substitutes the string `error`

- **ID:** jit_text_repeat_dispatch_and_silent_error_substitution_2026-08-01
- **Status:** partially fixed (`repeat` fixed; 51 sibling methods still missing)
- **Severity:** critical — silent, zero-exit data corruption that can reach files on disk
- **Engines affected:** Cranelift JIT (default engine). Tree-walking interpreter is correct.
- **Measured against:** origin `main` tip `5ca84bcefe5`, built in an isolated scratch
  extraction with its own `CARGO_TARGET_DIR` (the shared working copy was never touched).

## Summary

Two independent defects, landed separately.

1. **`text.repeat()` had no runtime definition at all.** `rt_string_repeat` was
   absent from BOTH runtimes (`src/compiler_rust/runtime/` and
   `src/runtime/runtime_native.c`), and `repeat` had no arm in the Cranelift
   method-dispatch table. `" ".repeat(4)` therefore raised
   `Runtime error: Function 'str.repeat' not found` and kept going.
2. **The unresolved-symbol fallback fabricated a value.**
   `rt_function_not_found` / `rt_method_not_found` printed a warning and then
   returned `RuntimeValue::from_special(tags::SPECIAL_ERROR)`. That sentinel
   renders as the six-character text `error` and reports `.len() == -1`, so the
   program continued with a fabricated string and **still exited 0**.

Defect 2 is the more dangerous half: it converts *every* backend dispatch gap
into silent data corruption, and 51 further text methods still reach it.

## Reproduction (PROVED)

`p3.spl`:

    fn main():
        val s = " ".repeat(4)
        print "LEN=" + s.len().to_text()
        print "VAL=[" + s + "]"

| engine | output | exit |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `LEN=4` / `VAL=[    ]` | 0 |
| `SIMPLE_EXECUTION_MODE=jit` (default) | `Runtime error: Function 'str.repeat' not found` / `LEN=-1` / `VAL=[]` | **0** |

The sentinel's rendering, measured directly (PROVED):

| expression (JIT, tip build) | result |
|---|---|
| `s.to_text()` | `error` |
| `print s` | `error` |
| `"X" + s + "Y"` | *(empty line — the whole concatenation is annihilated)* |
| `s.len()` | `-1` |

`LEN=-1` alongside a 5-character value is explained: `-1` is the length
`rt_len` reports for a non-heap special, and `error` is `io_print.rs`'s display
arm for `tags::SPECIAL_ERROR`. They are two different views of the same
sentinel, not two different values.

## Why it is urgent

`" ".repeat(n)` builds indentation for EasyFix **replacement text** in
`src/lib/nogc_sync_mut/tooling/easy_fix/rules_lint.spl`, and `simple fix` /
`simple fmt` dispatch through the same `src/app/cli/lint_entry.spl` entry as
`simple lint`. On the JIT route `simple fix` would write the literal word
`error` where indentation belongs — corrupting source files — and exit 0.

## Root cause 1: `repeat` dispatch

`.repeat()` lowers to `MethodCallStatic { func_name: "str.repeat" }`. The
Cranelift backend maps the method part of a dotted name to an `rt_*` runtime
function in a `match` in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` (and a parallel table in
`codegen/instr/closures_structs.rs`). `repeat` had no arm, fell through to
`_ => None`, failed cross-module resolution, and ended at `rt_function_not_found`.

This was **not** the "guard predicated on un-threaded static type info" shape of
the `rt_text_cmp_any` defect (`6469d70eb4e`) — the arm did not exist, and
neither did the runtime function it would have named. Verified in both runtimes:

    /usr/bin/grep -c rt_string_repeat  ->  0 in src/compiler_rust/runtime/**
                                           0 in src/runtime/runtime_native.c

Landing a text runtime method requires **seven** coordinated sites; missing the
last two is silent (the symbol is dead-stripped and the JIT drops the whole
module to the interpreter with a `[jit-fallback]` line):

1. `src/compiler_rust/runtime/src/value/collections.rs` — Rust implementation
2. `src/runtime/runtime_native.c` + `src/runtime/runtime.h` — C implementation (native lane)
3. `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — `RuntimeFuncSpec` signature
4. `src/compiler_rust/compiler/src/codegen/instr/calls.rs` — Cranelift method table
5. `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` — closure/dynamic table
6. `src/compiler_rust/runtime/src/value/mod.rs` — `pub use` re-export (**without this the
   `#[no_mangle]` symbol is garbage-collected out of the driver's `.dynsym`**)
7. `src/compiler_rust/common/src/runtime_symbols.rs` — `RUNTIME_SYMBOL_NAMES`

## Root cause 2: the `error` substitution

`src/compiler_rust/runtime/src/value/sffi/error_handling.rs`. Both entry points
returned `RuntimeValue::from_special(tags::SPECIAL_ERROR)`. Its unit tests
*asserted* that return value, so the silent behavior was pinned by the suite.

Fixed: the lookups now print the diagnostic and `std::process::exit(70)`
(`EX_SOFTWARE`). A missing symbol is a code-generation defect, never a
recoverable program condition. The tests that pinned the sentinel return were
replaced with tests on the diagnostic wording (they were asserting the bug).

## Root cause 3 (found while fixing): interpreter panics on a negative count

`"x".repeat(-2)` PANICKED the interpreter with `capacity overflow`, on both the
old and new builds, because `interpreter_method/string.rs` read the count with
`eval_arg_usize`, which does `as usize` on a negative `i64` and yields
`18446744073709551614`. Fixed at the arm by reading a signed int and clamping,
matching the pure-Simple `str_repeat` (`src/lib/common/string_core.spl`) and the
new `rt_string_repeat` in both runtimes: a non-positive count yields `""`.

## The family: 51 more text methods still return `error` under the JIT

Enumerated, not sampled: every method arm in
`src/compiler_rust/compiler/src/interpreter_method/string.rs` was turned into a
one-method probe and run under both engines (`/usr/bin/grep` pinned throughout —
the default `grep` here is ugrep). 102 probes; **52 fail under the JIT and
succeed on the interpreter**, one of which is a synthetic
`no_such_method_xyz` control. After the `repeat` fix, exactly one entry leaves
the list and 51 real methods remain:

    char_count up uppercase to_uppercase down lowercase to_lowercase capitalize
    swapcase title titlecase trim_left trim_right trim_start_matches
    trim_end_matches removeprefix remove_prefix removesuffix remove_suffix chomp
    squeeze rev reversed sorted taken take dropped drop skip push_str partition
    rpartition replace_first substr parse_i64 pad_left pad_start pad_right
    pad_end center zfill is_numeric is_alpha is_alphabetic is_digit
    is_alphanumeric is_alnum is_whitespace find_all find_indices ptr

Two distinct shapes are mixed in that list:

- **Missing aliases of a method that IS wired.** `to_upper`/`upper` are in the
  table but `up`/`uppercase`/`to_uppercase` are not; `trim_start` is wired but
  `trim_left` is not. Cheap to fix — table entries only, no new runtime code.
- **Genuinely absent runtime functions** (`char_count`, `capitalize`, `center`,
  `zfill`, `squeeze`, the `is_*` predicates, ...). These need the full
  seven-site treatment above.

Upper bound on repo exposure: `.<method>(` appears 603 times across
`src/lib`, `src/app`, `src/compiler` for 24 of the 51 names — but names like
`ptr` (321), `skip` (102) and `take` (51) collide with array/iterator methods,
so this is an **upper bound on text-receiver call sites, not a count** (INFERRED).

## Verification

Three binaries built from the same isolated tree and target dir, differing only
in the staged source files:

- **v0** = pristine `5ca84bcefe5`
- **v1** = v0 + `repeat` fix (7 sites) + interpreter negative-count clamp
- **v2** = v1 + loud `not found`

| probe | v0 JIT | v1 JIT | v1 interp | v2 JIT |
|---|---|---|---|---|
| `" ".repeat(4)` len / value | `-1` / `error` | `4` / `[    ]` | `4` / `[    ]` | `4` / `[    ]` |
| `"ab".repeat(3)` | not found | `ababab` | `ababab` | `ababab` |
| `"x".repeat(0)` | not found | `` | `` | `` |
| `"x".repeat(-2)` | not found | `` | `` (was a PANIC in v0) | `` |
| `"q".repeat(1)` | not found | `q` | `q` | `q` |
| `"é".repeat(3)` (UTF-8) | not found | `ééé` | `ééé` | `ééé` |
| **control** `.no_such_method_xyz()` | `error`, **exit 0** | `error`, exit 0 | semantic error, exit 1 | **exit 70**, loud |

Anti-false-green controls actually run:

- **True-positive control.** `no_such_method_xyz` still fires on both engines in
  v1, so "the engines now agree" is not agreement-by-silence.
- **De-JIT control.** `SIMPLE_JIT_STRICT=1` on v1 prints `JITMARK=[abab]` and
  exits 0 — the repeat path is genuinely JIT-compiled, not a whole-module drop to
  the interpreter. The same command on v0 still fails. No `[jit-fallback]` line
  appears in any v1 repeat run.
- **Old binary vs new tree.** v0 and v1 were built from the same tree with only
  the staged files swapped, so the delta is attributable to the fix, not source drift.
- **Scoped-diff control.** The 102-probe sweep differs between v0 and v1 by
  exactly one line (`repeat`). The fix changed nothing else.
- **Harness self-check.** The first sweep run emitted a probe that referenced an
  undefined variable, which made all 102 probes "fail" identically and would have
  reported `repeat` as broken on BOTH engines. Caught by contradiction with the
  hand-written probe. The matcher was then narrowed to
  `(Function|Method) '...' not found`.

## Follow-ups (not done here)

1. Wire the remaining 51 text methods. Start with the pure-alias subset — table
   entries only.
2. Sweep array / dict / option receivers the same way; the `error` sentinel is
   receiver-agnostic, so the same silent substitution is expected there.
3. `eval_arg_usize` (`interpreter_helpers/args.rs`) casts negative `i64` with
   `as usize` for every caller, not just `repeat`. Two more call sites in
   `interpreter_method/string.rs` (lines 187, 191) take the same argument and
   should be audited for the same panic.
