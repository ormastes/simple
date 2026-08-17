# Seed JIT: `text.to_i64()` / `.to_int()` return a FLOAT-tagged value — silent wrong results

## VERIFIED FIXED 2026-08-17 — does not reproduce

Classified by **content and execution**, not by SHA ancestry (per the
batch brief's correction: cited commits are not reachable from `origin/main`,
so "closed by commit X" proves nothing in either direction).

Executed against the deployed `bin/simple` under `SIMPLE_EXECUTION_MODE=jit`:

```
print("42".to_i64())   # => 42     (reported: 0.00000000000000000)
print("42".to_int())   # => 42     (reported: 0.00000000000000000)
val v = "42".to_i64()
print(v == 42)         # => true   (reported: false)
print("-5".to_i64())   # => -5     (reported: <special:2305843009213693951>)
```

Root cause of the fix, found in current source: `hir/lower/expr/mod.rs` now
carries `"to_int" | "to_i64" => Some(TypeId::I64)` in the string-method result
type table. The bug's own analysis was right that the parse was always correct
and only the decode was wrong; typing the method makes MIR emit the int-boxing
that `rt_println_value` needs, so the raw i64 is no longer decoded by bit
pattern.

**Caveat worth recording:** that same fix arm originally also covered
`parse_int`, which fixed this bug but ENTRENCHED
`parse_family_strips_option_jit_native_2026-08-02.md` by typing an
Option-returning method as `i64`. The two are the same site. Fixing this one
without the other is what made the second one durable — see that file.

## VERIFIED FIXED 2026-08-17 (batch_02 core-silent-wrong lane) — does not reproduce

The reproduction block below was re-run **verbatim** and every value is now
correct, on BOTH engines, on BOTH the deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, mtime 2026-08-16 22:59) and a
seed freshly built this session from `88227f48202`:

```
print("42".to_i64())   -> 42     (doc: 0.00000000000000000)
print("42".to_int())   -> 42     (doc: 0.00000000000000000)
print(v + 1)           -> 43     (doc: <special:5>)
print(v == 42)         -> true   (doc: false)
print("-5".to_i64())   -> -5     (doc: <special:2305843009213693951>)
```

Attributed fix: `2a240d9b0b2` ("fix(jit): i64 values >= 2^60 silently became a
different number"), whose message records adding "the missing STRING receiver
branch to the methods.rs numeric-cast dispatch, which handed back a string's
heap pointer as a 'successful' integer". That is this defect's tag/value
confusion. Note the fix predates neither binary tested, so this is not a
stale-binary artefact in either direction.

Closeable. The 2026-08-17 triage line "no retag landed" was a source-inspection
inference (it read a stale comment at `closures_structs.rs:1379`) and was not
confirmed by execution.

- **Status:** OPEN (pre-existing; found while landing an unrelated interpreter-lane fix)
- **Severity:** high — silent wrong values, not a crash. `"42".to_i64() == 42`
  evaluates to **false**.
- **Lane:** Rust bootstrap seed, **JIT (cranelift) lane**. `bin/simple run` is
  JIT-first with an interpreter fallback — an invocation that fails to compile
  prints `[INFO] JIT compilation failed, falling back to interpreter`. The
  reproduction below printed no such line, so JIT compilation succeeded and the
  program ran on the JIT lane. That is how the lane is attributed here.
- **NOT affected:** the seed tree-walk **interpreter** lane, which handles the
  method correctly (see "Lane split" below).

## Reproduction

Against the deployed, **unpatched** `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, self-identifies as the Rust
bootstrap seed via its startup WARNING):

```
fn main():
    print("42".to_i64())     # => 0.00000000000000000
    print("42".to_int())     # => 0.00000000000000000
    print(int("42"))         # => 42          (CORRECT)
    val v = "42".to_i64()
    print(v + 1)             # => <special:5>
    print(v == 42)           # => false       (SILENT WRONG)
    print("-5".to_i64())     # => <special:2305843009213693951>
```

## Bit-pattern evidence

- `"42".to_i64()` prints `0.00000000000000000`. That is `f64::from_bits(42)`
  = 2.08e-322, a subnormal double, rendered with fixed precision. The integer
  payload **42 is correct**; it is the *tag* that is wrong — the raw i64 is
  being interpreted as an IEEE-754 double.
- `"-5".to_i64()` prints `<special:2305843009213693951>` =
  `0x1FFF_FFFF_FFFF_FFFF`, i.e. the raw bits fall into the NaN-box "special"
  range rather than the integer range.
- `v + 1` printing `<special:5>` shows the corruption propagates through
  arithmetic, not just through `print`.

So the defect is a **tag/box** defect, not a parse defect: the parse produces
the right integer and the boxing step marks it as float/special.

## Why the JIT lane specifically

In codegen, `to_int` / `to_i64` / `parse_int` are rewritten to the runtime
symbol `rt_string_to_int`:

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1236`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:2793`, `:3226`
- `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:190`
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:1941`, `:2098`

`rt_string_to_int` (`src/compiler_rust/runtime/src/value/collections.rs:2356`)
returns a **bare `i64`**, deliberately strict (whole-string `str::parse`,
0 on failure) precisely because it backs these method calls. The returned raw
i64 is then not re-tagged as an integer before it re-enters the boxed value
domain.

Contrast: `int("42")` is CORRECT because the `int()` cast routes to the sibling
`rt_string_to_int_lenient` (`collections.rs:2387`) through a different lowering
that does tag its result.

## Lane split (important when reproducing)

| Lane | `"42".to_i64()` path | Result | Evidence |
|------|----------------------|--------|----------|
| JIT / cranelift | `sffi_alias_target` → `rt_string_to_int` (raw i64) | **BROKEN** (float-tagged) | PROVEN by execution (above) |
| Seed interpreter | `interpreter_method/string.rs:323` — `s.trim().parse::<i64>()` → `Value::Int(n)`, `Value::Int(0)` on error | expected correct | INFERRED from source only; not executed in isolation |
| Native / LLVM | `codegen/llvm/emitter.rs:190` → `rt_string_to_int` | unknown | NOT TESTED; shares the JIT alias so likely the same |

Note that the interpreter row is a source reading, not a measurement: forcing
the interpreter lane in isolation was not attempted here. A second divergent
copy of the method also exists at `interpreter_helpers/method_dispatch.rs:105`,
which returns `Value::Nil` on a parse failure where `string.rs:323` returns
`Value::Int(0)` — so the two interpreter paths do not even agree with each
other, and neither agrees with the strict `rt_string_to_int`. That three-way
disagreement is worth folding into the fix.

Because `bin/simple run` silently falls back from JIT to the interpreter when
JIT compilation fails, **the same program can print a different answer on two
runs**. Any A/B of this bug must pin the lane, or the fallback will look like
nondeterminism. This is also the most likely explanation for an earlier report
that the raw bits differed between two builds that both exhibited the bug.

## UNRESOLVED: the patched-vs-control bit difference

An earlier session reported that the raw bits of `"42".to_i64()` *differed*
between a patched and a control build, both of which exhibited the bug. That
claim could **not be reproduced or confirmed here**, and it is left open
deliberately rather than resolved by assertion in either direction.

Static analysis says the bits should be **identical**: the patch that session
was testing only adds interpreter `EXTERN_DISPATCH` entries, and `.to_i64()`
never consults that table, so the two builds should agree on this expression.

Working hypothesis, unproven: `bin/simple run` silently falls back from JIT to
the interpreter when JIT compilation fails, and the two lanes genuinely produce
different values here (JIT float-tagged, interpreter a correct `Int`). If the
two runs happened to take different lanes, the bits would differ for a reason
that has nothing to do with the patch. Anyone re-testing must pin the lane
first, or this will keep looking like nondeterminism.

## Relationship to the known tag-box family

Same family as the already-tracked defects: integers boxed with a `<<3` tag,
`Option<i64>` payload 3 colliding with nil, and the `char.to_i64()` tag-box
landmine. The common shape is a raw machine integer crossing a runtime boundary
without being re-tagged for the boxed value representation.

## Not caused by the interpreter EXTERN_DISPATCH fix

This was found while landing an interpreter-lane fix that registers
`rt_string_to_int` and `rt_raw_i64_to_string` in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`'s `EXTERN_DISPATCH`.
That fix is **interpreter-only** and cannot reach the JIT lane where this bug
lives. The reproduction above is on the unpatched deployed binary, which proves
the defect pre-exists that change.

## Suggested fix direction

Re-tag the `rt_string_to_int` return value as an integer at the call-site
lowering in the codegen paths listed above, the same way the
`rt_string_to_int_lenient` (`int()` cast) lowering already does. Add a
regression assertion that `"42".to_i64() == 42` is **true** on every engine,
since equality — not `print` — is the sharpest detector.

## Harness note: `build/sffi/libspl_winit.so` must exist

Unrelated to the tag bug but repeatedly costly: `GuiRenderer` returns
`no-gui-runtime` when `build/sffi/libspl_winit.so` is absent. The file is
present in the main repo checkout but is **absent in fresh `git worktree`
checkouts**, which has silently produced false "no GUI available" conclusions.
Before concluding a GUI lane is unavailable, verify that file exists in the
tree you are actually running from.

## Related divergence spotted (not yet a bug, but inconsistent)

The extern `rt_raw_i64_to_string` is declared with **two different return
types** in Simple source:

- `src/lib/common/ui/wm_app_process_contract.spl:7` — `-> text`
- `src/runtime/simple_core/core_bdd.spl:5` — `-> i64` (raw handle ABI)

`core_bdd.spl` is the native/freestanding SPipe BDD subset and does not run
through the seed interpreter, so the two do not collide today. If that file
ever runs interpreted, the declarations disagree about the encoding.

## REPRODUCED AND FIXED 2026-08-17

### Reproduced on a freshly built seed

Seed built from current `src/compiler_rust` in an isolated `CARGO_TARGET_DIR`
(`cargo build --release --bin simple`, `BUILDRC=0`, binary 2026-08-17 08:15;
rc read on the line AFTER the command, never through a pipe).
Probe: `test/01_unit/compiler/codegen/probe_any_typed_value_consumption_jit.spl`.

    SIMPLE_EXECUTION_MODE=jit   (BEFORE)
      PASS text_to_i64_direct
      FAIL text_to_i64_after_trim    got=2887700398081 want=42
      FAIL text_to_i64_after_upper   got=2887700397953 want=42
      PASS text_to_i64_after_replace
    SIMPLE_EXECUTION_MODE=interpreter (control arm, correct throughout)
      PASS on every entry

The returned values are HEAP POINTERS (they change between runs — an earlier
run on the deployed seed produced 5214297603201/5214297603425), not a
float-tagged number as the title says. Exit 0, no error, no warning.

The UNCHAINED form `"42".to_i64()` was always correct: it records a STRING
receiver type, so `to_int` takes the `from_ty == TypeId::STRING` branch that
routes to `rt_string_to_int`. The CHAINED form has no recorded receiver type
and the numeric-cast block defaults a missing type to `TypeId::I64`
(`unwrap_or(TypeId::I64)`), falling into the generic raw-register conversion
that hands back the intermediate text's pointer.

### Root cause

`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`,
`builtin_method_result_type` (definition at :1390, called at :600, :642, :1116).

That helper already existed and was written for exactly this defect, but every
text-in/text-out method was gated on `receiver_ty == Some(TypeId::STRING)` —
i.e. it declined to classify precisely when the receiver type was unknown,
which is the only situation a chained builtin can produce. It was therefore
inert for its own motivating case. (This also explains the triage note "no
retag landed": the doc comment there describes the fix, not the bug.)

### Fix

Split the arm. `trim`/`trim_start`/`trim_end`/`to_upper`/`to_uppercase`/
`to_lower`/`to_lowercase`/`char_at`/`replace` exist on a text receiver and on
NO other receiver, so classifying their result as `TypeId::STRING`
unconditionally cannot mis-type anything else. `substring`/`slice`/`concat`
stay receiver-gated because they are shared with array receivers, where the
result is an array rather than text.

### After — same probe, same freshly built seed, patch applied (BUILDRC=0)

    SIMPLE_EXECUTION_MODE=jit
      PASS text_to_i64_direct
      PASS text_to_i64_after_trim
      PASS text_to_i64_after_upper
      PASS text_to_i64_after_replace
    SIMPLE_EXECUTION_MODE=interpreter
      ANY_TYPED_CONSUMPTION PROBE: ALL PASS

### Specs

- reproducing: `test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl`
- class detection: `test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl`
- shared run-path probe: `test/01_unit/compiler/codegen/probe_any_typed_value_consumption_jit.spl`

Both specs shell out to the probe under BOTH engines, because a spec body runs
INTERPRETED and the interpreter was correct here throughout — an in-process
example can never go red on this defect.

### Shared root cause with two sibling rows

This is one of three separately-filed P1 rows that are the same defect class:
an ANY-typed value reaching a consumption site that handles the raw tagged
word instead of decoding it. See
`untyped_list_element_read_seed_rootcause_2026-07-30.md` (already fixed
in-tree) and `untyped_fn_result_erased_to_zero_2026-08-01.md` (still live).

### Spec-level RED -> GREEN (both quoted, same spec file, same test runner)

The only variable between the two runs is `SIMPLE_BIN`, i.e. which seed the
spec's subprocess executes. `SPECRC` was assigned on the line AFTER the
command, never through a pipe.

    SIMPLE_BIN = deployed seed (defect present)
      SPEC FILE VERDICT: ... declared>=3 executed=3 passed=1 failed=2 dropped=0
      Results: 3 total, 1 passed, 2 failed
      SPECRC=1

    SIMPLE_BIN = seed built from current source WITH the patch (BUILDRC=0)
      SPEC FILE VERDICT: ... declared>=3 executed=3 passed=3 failed=0 dropped=0
      Results: 3 total, 3 passed, 0 failed
      SPECRC=0

`executed=3` in both runs, so neither verdict is vacuous.

Host note: an earlier attempt at the RED run, made while 99 `simple` processes
were live, returned `timeout=1 reason=daemon-no-response` with no `Results:`
line. That is UNVERIFIED, not RED — it is not quoted as evidence above. The
RED line above comes from a later, completed run.
