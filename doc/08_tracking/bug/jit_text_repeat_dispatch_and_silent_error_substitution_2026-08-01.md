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

---

# Update 2026-08-01 (follow-up lane): 51 -> 43

## The inherited harness could not tell the two engines apart

The 102-probe sweep classified a method as interpreter-OK/JIT-broken with
`jnf>0 && inf==0`, where both columns counted the regex
`(Function|Method) '[^']*' not found`. The interpreter does not use that
wording. It emits:

    error: semantic: method `no_such_method_xyz` not found on type `str`

backticks, lowercase, and no `Function '...'`. So `inf` was **0 for every one of
the 102 probes, including the deliberate `no_such_method_xyz` control**. The
control row reads `NOSUCHMETHOD_CONTROL 1 0 0` -- it "passed" only because the
interpreter half was structurally incapable of firing. The interpreter column
carried no information at all.

Reclassified on printed success (`^OK$`) per engine instead, since **every probe
exits 0 regardless** -- exit status is unusable here. Both self-checks now
behave:

| probe | JIT | interpreter |
|---|---|---|
| `NOSUCHMETHOD_CONTROL` (must fail both) | FAIL | FAIL |
| `SELFCHECK_GOOD` = `s.upper()` (must pass both) | PASS | PASS |

Re-measured at `e482a8e1af39`: **51 FAIL/PASS, 51 PASS/PASS, 1 FAIL/FAIL**. The
51 are byte-identical to `missing51.txt`, so the count survived the correction
-- no method fails on both engines. PROVED.

`git diff 73a041794404 e482a8e1af39 -- src/compiler_rust src/runtime` is empty,
so the sibling's binaries are still current-tip-accurate for these files.

**Scope limit of the sweep:** it proves *dispatch existence*, not correctness. It
cannot see a wrong mapping. Example already in the tree: `reverse` maps to
`rt_array_reverse` (the ARRAY reverse) yet "passes".

## Landed: 8 aliases

`up`, `uppercase`, `to_uppercase` -> `rt_string_to_upper`; `down`, `lowercase`,
`to_lowercase` -> `rt_string_to_lower`; `trim_left` -> `rt_string_trim_start`;
`trim_right` -> `rt_string_trim_end`. Two dispatch sites only (`calls.rs`,
`closures_structs.rs`) -- aliases need no new runtime function, so the five
silent sites do not apply. Values verified equal on both engines (`up`/`uppercase`
/`to_uppercase` all `AB`, `trim_left` `[x  ]`, `trim_right` `[  x]`).

**51 -> 43.**

## `parse_i64` was deliberately NOT wired -- it exposed an existing defect

`parse_i64` is in the interpreter's `parse_int | parse_i32 | parse_i64` arm, so
it looked like a free alias of the already-wired `parse_int`. Wiring it made the
sweep go to 42. That was a false green in *this lane's own measurement*, caught
only by a value spot-check:

    "42".parse_i64() + 1   JIT: 43     interpreter: type mismatch: cannot convert enum to int

The interpreter's `parse_*` returns an **Option** (`Value::some`/`Value::none`,
string.rs:354); `rt_string_to_int` returns a raw `i64`. So the pre-existing
`parse_int -> rt_string_to_int` entry is **already wrong** and silently strips
the Option -- reproduced on the unmodified baseline binary, so it is not
introduced here. Adding `parse_i64` would have spread that defect to a second
spelling. Reverted; the count is honestly 43, not 42.

**Open defect:** `parse_int` / `parse_float` / `parse_f64` / `parse_f64_safe`
strip the Option on the JIT. Needs Option-returning runtime entry points, not a
table edit.

## Fixed: `eval_arg_usize` negative-argument panic (all 21 call sites)

`Ok(eval_arg_int(...)? as usize)` turned `-5` into 18446744073709551611. Callers
compare `current_len >= width` (false against a huge width) and then allocate the
difference:

    "ab".pad_left(-5)   ->   PANIC capacity overflow (raw_vec/mod.rs:554)

This is a **second instance beyond the sibling's `repeat`**, found by probing the
family rather than the one reported method. Fixed centrally by saturating
negatives to 0, which repairs all 21 call sites (10 in `interpreter_method/
string.rs`, 9 in `collections.rs`, 2 in `interpreter_helpers/patterns.rs`) at
once:

| probe (interpreter) | before | after |
|---|---|---|
| `"ab".pad_left(-5)` | PANIC capacity overflow | `ab` |
| `"ab".take(-2)` | `ab` (wrapped to usize::MAX) | `` |
| `"ab".drop(-2)` | `` | `ab` |
| `"ab".substr(-1, 2)` | `` | `ab` |

## Correction to a standing assumption about pure-Simple codegen

It has been suggested that `src/compiler/50.mir/_MirLoweringExpr/
method_calls_literals.spl` special-cases only a handful of text methods and has
no `str.* -> rt_*` table. It does have one, with **62** `rt_string` references.
The real gap is narrower but real: its guard admits only

    trim strip lower to_lower to_upper split replace rfind find contains parse_f64

`upper` is not in that list, nor are any of the 8 aliases landed here. **So these
fixes do not reach pure-Simple codegen** -- confirmed as a third work item, in a
different codegen from the two dispatch sites above.

## Remaining 43

Alias class is exhausted; every one of the 43 needs a real runtime function in
**both** the Rust runtime and `src/runtime/runtime_native.c`, plus the five other
wiring sites. Groups: case (`capitalize`, `swapcase`, `title`, `titlecase`),
affix (`trim_*_matches`, `remove{,_}prefix/suffix`, `chomp`), sequence (`rev`,
`reversed`, `sorted`, `take{,n}`, `drop{ped}`, `skip`, `squeeze`), split
(`partition`, `rpartition`, `find_all`, `find_indices`), pad (`pad_left/start/
right/end`, `center`, `zfill`), predicate (`is_*`), and misc (`char_count`,
`push_str`, `replace_first`, `substr`, `parse_i64`, `ptr`).

---

# Update 2026-08-01 (batch 2): 43 -> 36, and the wiring list is EIGHT sites

## Landed: 7 `is_*` predicates via 4 runtime functions

`is_numeric` and `is_digit` have the same ASCII-digit body in the interpreter,
and `is_alpha`/`is_alphabetic` and `is_alphanumeric`/`is_alnum` are pairs, so
seven spellings collapse to four entry points: `rt_string_is_digit`,
`rt_string_is_alpha`, `rt_string_is_alnum`, `rt_string_is_whitespace`.
Implemented in **both** runtimes (Rust `value/collections.rs` and C
`runtime_native.c` + `runtime.h`), per the rt_at/rt_array_at precedent.

Semantics matched to the interpreter: the empty string is FALSE for every class.

**43 -> 36.**

## The seven-site list is incomplete: a bool-returning method needs an EIGHTH

All seven known sites were wired correctly and the sweep went green -- but the
values were wrong on the JIT:

    "123".is_digit()   JIT: nil     interpreter: true
    "12a".is_digit()   JIT: 0       interpreter: false

Truthy misdecoded as `nil`, falsy printed as the raw untagged `0`. The missing
site is the result-type table at `hir/lower/expr/mod.rs:1096`. Without an entry
there the call is typed `TypeId::ANY` and the bool-boxing step at the
print/call-arg lowering site is skipped.

This is the *same defect* as bug `jit_bool_result_type_gap_2026-07-29` (lane
BOOLRESULT), which fixed exactly this for `is_empty`. The comment recording that
fix sits three lines above the arm that had to be edited again here -- the fix
enumerated the one reported method rather than the family, so the next
bool-returning text method to be wired hit it again.

**Site 8 of 8 (bool-returning methods only): `hir/lower/expr/mod.rs`, the
`Some(TypeId::BOOL)` arm.** Like the `value/mod.rs` re-export and
`RUNTIME_SYMBOL_NAMES`, it is SILENT when missed -- worse than silent here,
since the 102-probe sweep reports PASS.

Also noted while tracing it: `closures_structs.rs` has a *second* dispatch table
at :1359 besides the one at :1487, and the LLVM backend has two more
(`codegen/llvm/emitter.rs:174`, `codegen/llvm/functions.rs:2368`). Those were not
needed for this batch but belong in the site list for anyone wiring the
remaining 36.

## Confirmed limit of the sweep

Both `parse_i64` (batch 1) and the `is_*` predicates (batch 2) were scored PASS
by the 102-probe sweep while returning WRONG VALUES. The sweep proves dispatch
existence only. **Every batch needs a hand value-comparison across both engines
before it is claimed.** Both defects were caught that way and neither reached a
commit.

## Known divergence introduced, non-ASCII only

The C runtime has no Unicode tables, so `is_alpha`/`is_alnum`/`is_whitespace`
answer 0 for any byte >= 0x80, where the Rust runtime and the interpreter
classify per Unicode `char`. `is_digit`/`is_numeric` are ASCII-digit by
definition and agree exactly on all input. Documented in `runtime_native.c` at
the implementation; the native lane is the only one affected.
