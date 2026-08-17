# JIT text-method dispatch gap silently substitutes the string `error`

- **ID:** jit_text_repeat_dispatch_and_silent_error_substitution_2026-08-01
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  (`parse_i64`, `ptr`), both blocked on a decision rather than on transcription.
  See the batch 5 section at the end for why.
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

---

# Update 2026-08-01 (batch 3): 36 -> 21, measured on VALUES not on dispatch existence

Base sha `8dd8f17b656`. Three binaries from one isolated extraction and one
`CARGO_TARGET_DIR`, differing only in staged source.

## The harness was replaced, again

The inherited 102-probe sweep is not used here at all. It classifies on the
presence of a diagnostic, and both previous batches were scored PASS by it while
returning wrong values. This lane compares the **printed value** from each
engine against a hand-computed expectation, and reports four outcomes
(`PASS` / `JIT-BROKEN` / `INTERP-BROKEN` / `BOTH-BROKEN`). A wrong value is a
FAIL, not a pass. Exit status is never consulted -- every probe exits 0.

Two controls run in every sweep and both behaved on every run:

| control | requirement | v0 | v1 |
|---|---|---|---|
| `MUSTFAIL_CONTROL` = `.no_such_method_xyz()` | must produce NO value on either engine | fails both | fails both |
| `MUSTPASS_CONTROL` = `"ab".upper()` | must produce `AB` on both | PASS | PASS |

## Landed: 15 methods via 11 new runtime functions in BOTH runtimes

`char_count`, `capitalize`, `swapcase`, `title`, `titlecase`, `chomp`,
`trim_start_matches`, `trim_end_matches`, `removeprefix`, `remove_prefix`,
`removesuffix`, `remove_suffix`, `squeeze`, `push_str`, `replace_first`.

New entry points: `rt_string_char_count`, `rt_string_capitalize`,
`rt_string_swapcase`, `rt_string_title`, `rt_string_chomp`,
`rt_string_trim_start_matches`, `rt_string_trim_end_matches`,
`rt_string_remove_prefix`, `rt_string_remove_suffix`, `rt_string_squeeze`,
`rt_string_replace_first`. `push_str` needs no new function -- text is
immutable here, so it is exactly the existing `rt_string_concat`.

All eight wiring sites were used. `char_count` returns `i64` and the other
fourteen return `str`, so all fifteen needed the `hir/lower/expr/mod.rs`
result-type entry that batch 2 identified as site 8 -- it is not bool-specific,
it is required for **every** result type that needs boxing.

### Value evidence (PROVED)

26-probe run, `v0` = pristine `8dd8f17b656`, `v1` = v0 + this batch:

| | v0 | v1 |
|---|---|---|
| non-green rows | **24 of 24 real probes JIT-BROKEN** | **0** |
| controls | both correct | both correct |

v0's JIT half printed no value at all and emitted
`Runtime error: Function 'str.capitalize' not found` followed by the loud
`unresolved symbol` exit added earlier in this bug. v1 matches the interpreter
byte-for-byte on all 24, including `"héllo".char_count() == 5` (codepoints, not
bytes) and `"héllo"`-class UTF-8 in `squeeze`.

### Non-vacuity controls actually run (PROVED)

- **Sabotage of the IMPLEMENTATION, not a shim.** `rt_string_capitalize`'s body
  in `runtime/src/value/collections.rs` was made to return `SABOTAGE`, rebuilt,
  and the JIT probe printed `R=[SABOTAGE]` while the interpreter still printed
  `R=[Hello world]` and the neighbouring `swapcase` probe still printed
  `R=[AbC9]`. The compiled lane genuinely executes this function body.
- **De-JIT control.** `SIMPLE_JIT_STRICT=1` on v1 still prints the value and no
  `[jit-fallback]` / "dropped to the interpreter" line appears, so this is not a
  whole-module drop to the interpreter.
- **C runtime measured, not just compiled.** The C half is unreachable from the
  seed, so it was linked into a direct harness
  (`runtime_native.c` + siblings) and every one of the 23 C cases printed the
  same bytes as the interpreter and the JIT -- including the UTF-8 `squeeze`
  case, which a byte-wise implementation would have got wrong.

### Divergence introduced (documented at the implementation)

The C runtime still has no Unicode tables, so `capitalize`/`swapcase`/`title`
change case for **ASCII letters only** and pass bytes >= 0x80 through unchanged,
where the Rust runtime and the interpreter apply full Unicode case mapping.
Same trade-off and same reason as the `is_alpha`/`is_alnum`/`is_whitespace`
divergence from batch 2. The other nine functions (`char_count`, `chomp`, the
two `trim_*_matches`, the two `remove_*fix`, `squeeze`, `replace_first`) are
codepoint- or byte-exact and agree on all input, non-ASCII included -- `squeeze`
in particular decodes UTF-8 rather than comparing bytes, precisely so it does not
diverge.

## Remaining 21

    rev reversed sorted taken take dropped drop skip
    pad_left pad_start pad_right pad_end center zfill
    partition rpartition find_all find_indices substr
    parse_i64 ptr

Grouped by the obstacle that is actually distinct, not by name:

- **Receiver-polymorphic (8):** `rev`, `reversed`, `sorted`, `take`, `taken`,
  `drop`, `dropped`, `skip` are ALSO array methods
  (`interpreter_method/collections.rs`), and the `calls.rs` table is keyed on the
  method name alone with no receiver type. A text-only mapping would silently
  give an array receiver a text answer -- trading a loud failure for a wrong one.
  These need receiver-dispatching entry points, the `rt_at`/`rt_array_at`
  precedent. Note the tree ALREADY has this defect for `reverse`, which is mapped
  to `rt_array_reverse` for every receiver.
- **Optional-argument (6):** the pad family takes an optional pad character.
  A missing argument is padded with tagged nil (bit pattern 3) by
  `adapt_args_to_signature`, which is safely detectable for a TEXT parameter
  (not a heap string) -- the mechanism `squeeze` already uses here.
- **Array-returning (4):** `partition`, `rpartition`, `find_all`,
  `find_indices`. `partition` is also an array method, so it inherits the
  receiver-polymorphism problem.
- **`substr` (1):** the optional argument is an INT, and tagged nil IS the
  integer 3, so "absent" and "3" are indistinguishable at the callee. Needs
  arity-aware dispatch (two entry points selected on `args.len()`), not a
  sentinel.
- **`parse_i64` (1):** still blocked on the pre-existing `parse_*` Option/raw-i64
  mismatch documented in batch 1. Unchanged; not papered over.
- **`ptr` (1):** returns a raw address into a thread-local pin cache
  (`PINNED_STRINGS`). It is an SFFI escape hatch whose interpreter semantics
  (pin a copy for the process lifetime) have no meaningful compiled-lane
  equivalent -- the compiled string's buffer is already stable. Needs a decision,
  not a transcription.

---

# Update 2026-08-01 (batch 4): 21 -> 12

## Landed: 9 methods via 7 new runtime functions in BOTH runtimes

`pad_left`, `pad_start`, `pad_right`, `pad_end`, `center`, `zfill`, `find_all`,
`find_indices`, `substr`.

New entry points: `rt_string_pad_left`, `rt_string_pad_right`,
`rt_string_center`, `rt_string_zfill`, `rt_string_find_all`,
`rt_string_substr`, `rt_string_substr_from`.

### The optional-argument problem has TWO answers, not one

- **Optional TEXT argument (the pad character):** safe to default inside the
  runtime. `adapt_args_to_signature` pads a missing argument with tagged nil,
  which is not a heap string, so the callee's "is this text?" test already
  answers "no". `pad_left`/`pad_right`/`center` and batch 3's `squeeze` all use
  this.
- **Optional INT argument (`substr`'s length):** NOT safe. Tagged nil is
  `TAG_SPECIAL(3) | SPECIAL_NIL(0)` = the 64-bit value **3**, which is
  indistinguishable from the integer 3 in an int slot. A sentinel here would
  have made `"abcdefgh".substr(3)` return three characters instead of five --
  a silent wrong answer, exactly the class of bug this document exists for. It
  is dispatched on `args.len()` to two symbols instead
  (`rt_string_substr` / `rt_string_substr_from`), and the collision case is a
  probe: `"abcdefgh".substr(3)` -> `defgh` and `"abcdefgh".substr(0, 3)` ->
  `abc` on both engines. PROVED.

`substr` is char-indexed in both new symbols, deliberately NOT routed to the
byte-indexed `rt_slice`. The stale comment in `hir/lower/expr/mod.rs` that
listed `substr` as NEEDS-RUNTIME for exactly this reason is updated in place;
`take` still carries that status because it is also an array method.

### Value evidence (PROVED)

25 real probes + the same 2 controls, run against pristine `8dd8f17b656` and
against the new build:

| | v0 | v2 |
|---|---|---|
| non-green rows | **25 of 25 JIT-BROKEN** | **0** |
| controls | both correct | both correct |

Batch 3's 24 probes were re-run on the same binary and are still green, so this
batch regressed nothing.

The harness caught **three wrong expectations of its own** before they could
become false claims: `pad_right` (trailing spaces), `center` with an odd
padding total (the extra character goes on the RIGHT: `"ab".center(5,"-")` is
`-ab--`, not `--ab-`), and array `.to_text()`, which returns the empty string
here so the `find_all` probes had to compare elements and length instead. A
harness that only compared the two engines to each other would have called all
three PASS.

### C runtime measured, not just compiled (PROVED)

All 23 C cases printed the same bytes as the interpreter and the JIT, including
`substr` on a multi-byte receiver (`"héllo".substr(1,2)` -> `él`) and a
multi-byte pad character (`"é".pad_left(3,"*")` -> `**é`). The C `find_all`
returns a 2-element array with elements 1 and 3.

### No new divergence

Every function in this batch is codepoint- or byte-exact; none needs a Unicode
table, so the C lane agrees with the other two on all input.

## Remaining 12

    rev reversed sorted taken take dropped drop skip partition rpartition
    parse_i64 ptr

Ten of the twelve are the receiver-polymorphic set (all also array methods) and
need `rt_at`-style receiver dispatch; `parse_i64` and `ptr` are the two
documented non-transcription cases.

---

# Update 2026-08-01 (batch 5): 12 -> 2

## Landed: 10 receiver-polymorphic methods via 6 new runtime functions

`rev`, `reversed`, `sorted`, `take`, `taken`, `drop`, `dropped`, `skip`,
`partition`, `rpartition`.

Every one of these names is ALSO an array method, and the dispatch tables in
`codegen/instr/{calls,closures_structs}.rs` are keyed on the method NAME with no
receiver type. Two different answers were needed, and picking the wrong one
would have been a silent wrong answer rather than a loud failure:

- **Receiver-dispatched in the runtime** (`rt_at`/`rt_array_at` precedent):
  `rt_reverse`, `rt_take`, `rt_drop`. Text reverses/takes/drops by CHARACTER,
  an array by ELEMENT. Implemented for both receivers in both runtimes.
- **Text-only, and LOUD on anything else:** `rt_string_sorted`,
  `rt_string_partition`, `rt_string_rpartition`. Ordering an array means
  ordering tag-boxed values of mixed type and the C runtime has no such
  comparator; the array `partition` takes a PREDICATE and returns
  `[passing, failing]` -- a different arity, argument type AND result shape, and
  it has to invoke a closure. A shared symbol would have had to guess. Instead
  `refuse_non_text_receiver` prints a diagnostic naming the method and exits 70,
  the same policy this bug already applies to an unresolved symbol.

`reverse` is deliberately NOT rerouted. It still points at `rt_array_reverse`,
which reverses IN PLACE and returns a bool for EVERY receiver including text.
That is a separate wrong mapping; changing it would also change
`arr.reverse()`'s return value, which is out of scope here. Verified unchanged:
`[1,2,3].reverse()` prints `[3, 2, 1]` on both engines on both binaries.

### Value evidence (PROVED)

30 real probes + the 2 controls. On pristine `8dd8f17b656`, 28 are JIT-BROKEN;
after this batch all 30 agree on both engines. The two that already passed on v0
are `[1,2,3].take(2)` and `[1,2,3].drop(1)` -- statically-typed array receivers
reach a different, already-working lowering, and they still produce the same
values after the change. Batches 3 and 4 (24 + 25 probes) were re-run on the new
binary and are still green.

### The loud-stays-loud control (PROVED)

`[1,2,3].partition(pred)` under the JIT:

| binary | behaviour |
|---|---|
| v0 | `Runtime error: unresolved symbol ...` (loud) |
| v3 | `Runtime error: str.partition was called on a receiver that is not text ...` (loud) |

Loud before, loud after, and the new message names the method and the reason. No
path was converted from a loud failure into a wrong value. `[3,1,2].sorted()`
with a statically-typed receiver is unaffected and still prints `[1, 2, 3]` on
both binaries -- the text-only symbol is a safety net for the erased-receiver
path, not the route a typed array takes.

### C runtime measured, not just compiled (PROVED)

All 21 C cases printed the same bytes as the interpreter and the JIT, including
`rev`/`take`/`drop` on multi-byte receivers and all three slots of
`partition`/`rpartition` in both the hit and miss cases, plus the array
receivers (`arr_rev` = 3 2 1, `arr_take` = 1 2, `arr_drop` = 2 3).

### Noticed in passing, NOT fixed here

The interpreter's array `partition` only matches `Value::Lambda`, so
`a.partition(named_fn)` returns `([], [])` instead of partitioning. Pre-existing
on the unmodified baseline and untouched by this change.

## Remaining 2 -- neither is a transcription job

- **`parse_i64`.** Still blocked on the pre-existing `parse_*` Option/raw-i64
  mismatch first recorded in batch 1: the interpreter's
  `parse_int | parse_i32 | parse_i64` arm returns an **Option**
  (`Value::some`/`Value::none`), while the already-wired
  `parse_int -> rt_string_to_int` returns a raw `i64` and silently strips it.
  Reproduced on the unmodified baseline, so it is not introduced here. Wiring
  `parse_i64` to the same symbol would spread a known defect to a third
  spelling. The fix is Option-returning runtime entry points for the whole
  `parse_*` family (`parse_int`, `parse_i32`, `parse_i64`, `parse_float`,
  `parse_f64`, `parse_f64_safe`), which is a different change from a table edit
  and should be its own lane.
- **`ptr`.** The interpreter pins a COPY of the string in a thread-local
  `PINNED_STRINGS` cache for the process lifetime and returns its address. On
  the compiled lanes the string's own buffer is already stable and registered,
  so the honest compiled equivalent is `rt_string_data`, not a second pinned
  copy -- but that is a semantic DECISION about an SFFI escape hatch (who owns
  the memory, how long it lives, whether the two engines should even agree),
  not a transcription of an interpreter arm. Wiring it without that decision
  would hand callers a pointer with different lifetime rules on each engine,
  which is precisely the silent-divergence class this document tracks.

## Site list, consolidated

Wiring one text method touches, in the worst case:

1. `runtime/src/value/collections.rs` -- Rust implementation
2. `src/runtime/runtime_native.c` + `src/runtime/runtime.h` -- C implementation
3. `compiler/src/codegen/runtime_sffi.rs` -- `RuntimeFuncSpec` signature
4. `compiler/src/codegen/instr/calls.rs` -- Cranelift method table
5. `compiler/src/codegen/instr/closures_structs.rs` -- closure/dynamic table
6. `runtime/src/value/mod.rs` -- `pub use` re-export (silent when missed)
7. `common/src/runtime_symbols.rs` -- `RUNTIME_SYMBOL_NAMES` (silent when missed)
8. `compiler/src/hir/lower/expr/mod.rs` -- result-type table (silent when missed,
   and the 102-probe sweep reports PASS anyway). Needed for EVERY result type
   that requires boxing, not just bool.

## Pre-existing test failures, proved pre-existing (PROVED)

`cargo test --release -p simple-runtime` reports **1080 passed, 7 failed** both
with batch 5 applied and on pristine `8dd8f17b656` with only the two runtime
source files reverted. Identical failure list, identical pass count:

    executor::tests::test_isolated_thread_spawn_with_args_and_join
    executor::tests::test_isolated_thread_spawn_with_args_and_join_direct_function_record
    loader::package::format::tests::test_manifest_section_rejects_partial_runtime_variants_trailer
    loader::settlement::native::tests::test_native_lib_manager
    value::collections::tests::test_dict_invalid_value
    value::collections::tests::test_low_heap_tagged_values_do_not_crash_collection_runtime
    value::heap::attr_tests::owner_attribution_orders_by_live_bytes_and_frees_settle

None of the three batches in this document adds a failure. They are recorded
here so a later lane does not attribute them to this work.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — PARTIALLY FIXED, 1 arm left

Of the two arms this doc recorded as unwired:

- **`repeat` is now wired.** `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2058`
  (`"repeat" => "rt_string_repeat"`) and `codegen/instr/calls.rs:3502`
  (`"repeat" => Some("rt_string_repeat")`).
- **The literal-`"error"` substitution is gone.** `grep -n '"error"' src/compiler_rust/compiler/src/codegen/instr/`
  returns zero hits, so nothing in the instr dispatch layer can substitute that string any more.
- **`reverse` is still unwired and STILL A REAL GAP.**
  `grep -n reverse src/compiler_rust/compiler/src/codegen/instr/methods.rs` returns zero hits, and
  `rt_string_reverse` does not exist anywhere in `src/compiler_rust/runtime/src` or `src/runtime`
  — the only near-match is the file-local C helper `rt_string_reverse_chars`
  (`src/runtime/runtime_native.c:4644`), which is `static` and not an exported runtime symbol.
  Closing this requires a new exported runtime function (outside `src/compiler_rust/compiler/**`),
  so it was not attempted by this lane. This is the same residual tracked by
  `jit_dispatch_worklist_2026-07-29.md`.
