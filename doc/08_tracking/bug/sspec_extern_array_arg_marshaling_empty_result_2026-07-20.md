# `bin/simple test` (in-process AND nested-subprocess) can silently turn `[u8]` (array) extern arguments into empty results — two distinct, same-shaped, NOT-yet-reconciled observations

- **Filed:** 2026-07-20
- **Status:** open (root cause narrowed for observation 1, not confirmed
  for observation 2 — see "Two observations" below; not fixed; not chased
  further, out of scope for the fix that found it)
- **Severity:** high — affects any extern function taking an array-typed
  argument called (directly or via a spawned `bin/simple run` subprocess)
  anywhere downstream of `bin/simple test`; silent (no error, no crash), so
  it can hide as "the function returns empty" instead of surfacing as an
  obvious bug
- **Found by:** side effect of diagnosing
  `doc/08_tracking/bug/char_from_code_non_ascii_unsupported_2026-07-20.md`
  (the `char_from_code_inline` / `char_from_codepoint` non-ASCII fix). This
  doc is the write-up of the marshaling gap itself, split out because it is
  a separate, more general defect than that fix's scope, and because a
  parallel lane is reportedly chasing the same symptom class ("imported
  functions returning EMPTY values under `simple test` but correct under
  `run`") independently. If that lane already has a doc for this, merge
  this repro into it instead of keeping both.

## Two observations — read before assuming one root cause

This doc originally claimed a single mechanism ("the SSpec `describe`/`it`
evaluator marshals `[u8]` differently"). That claim is **too narrow**:
testing the fix's subprocess-probe guard
(`test/03_system/interpreter/char_from_code_non_ascii_system_spec.spl`)
turned up a second occurrence of the identical symptom shape (correct bytes
in, `rt_bytes_to_text` silently returns empty, no error) in a context that
has **no SSpec `describe`/`it` block anywhere in the failing process** — a
plain `fn main():` script, executed as a genuinely separate `exec`'d OS
process. A cleanly `exec`'d child cannot inherit an *in-process*
interpreter-evaluator quirk from its parent, so observation 2 cannot be
fully explained by observation 1's "SSpec evaluator" theory as stated. They
are recorded here together because they are almost certainly related (same
extern, same argument type, same silent-empty signature, both confined to
being downstream of `bin/simple test`), but **the exact relationship
between them is not established** — do not assume they share one fix.

## Observation 1: in-process, inside an SSpec `it` block

An `extern fn` that takes an array argument (confirmed with `[u8]`) and is
called with an array literal constructed inline in Simple code:
- Under `bin/simple run <script>.spl` (a plain `fn main():` script, no
  SSpec): **works correctly**.
- Under `bin/simple test <spec>.spl` (an SSpec `describe`/`it` block calling
  the exact same extern with the exact same literal argument): **silently
  returns an empty/nil result** — no error, no crash, no diagnostic. The
  call itself does not fail; it just returns as if it had been given a
  null/zero-length array.

This is the well-isolated, root-cause-narrowed observation — see "Entry
point / mechanism" below for the `rt_core_as_array` guard-clause hypothesis.

## Minimal repro (observation 1)

Confirmed minimal, reduced independent of any UTF-8/text logic — this is
the extern-call/array-marshaling mechanism in isolation.

`extern fn rt_bytes_to_text(bytes: [u8]) -> text` is declared (with a real
backing C symbol, see "Entry point" below) and called with a 2-element
literal array.

**Run path — correct:**
```simple
extern fn rt_bytes_to_text(bytes: [u8]) -> text

fn main():
    val b: [u8] = [65u8, 66u8]
    val t = rt_bytes_to_text(b)
    print("len=" + t.len().to_string() + " text=[" + t + "]")
```
```
$ bin/simple run repro.spl
len=2 text=[AB]
```

**Test path — silently empty:**
```simple
extern fn rt_bytes_to_text(bytes: [u8]) -> text

describe "minimal rt_bytes_to_text marshaling repro":
    it "encodes a 2-byte array literal to text":
        val b: [u8] = [65u8, 66u8]
        val t = rt_bytes_to_text(b)
        print("SSPEC len=" + t.len().to_string() + " text=[" + t + "]")
        expect(t).to_equal("AB")
```
```
$ bin/simple test repro_spec.spl
SSPEC len=0 text=[]
  ✗ encodes a 2-byte array literal to text
    expected  to equal AB
Passed: 0
Failed: 1
```

Same extern, same literal argument, same seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, prints the "bootstrap seed
only" banner) invoked two different ways in the same process tree — one
correct, one silently empty.

## Entry point / mechanism (traced from source, not fully confirmed by breakpoint/debugger — next step for whoever picks this up)

`rt_bytes_to_text` is implemented in `src/runtime/runtime_native.c`:

```c
int64_t rt_bytes_to_text(int64_t bytes_value) {
    RtCoreArray* array = rt_core_as_array(bytes_value);
    if (!array || !array->data || array->len <= 0) {
        return rt_string_new(NULL, 0);   /* <-- silently empty, no error */
    }
    return rt_string_new((const uint8_t*)array->data, (uint64_t)array->len);
}
```

`rt_core_as_array` (same file, ~line 1175) treats its `int64_t` argument as
a **tagged heap pointer**:

```c
static inline RtCoreArray* rt_core_as_array(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;   /* <-- rejects small/raw integers */
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        raw &= ~RT_VALUE_TAG_MASK;
    } else if ((raw & RT_VALUE_TAG_MASK) != 0) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)raw;
    if (a->kind != RT_VALUE_HEAP_ARRAY) return NULL;
    ...
}
```

Leading hypothesis: under `bin/simple run`, the array literal is marshaled
into a real tagged heap pointer (`RT_VALUE_TAG_HEAP`-tagged address of an
`RtCoreArray`) before crossing the extern-call boundary, which
`rt_core_as_array` accepts. Under the SSpec `describe`/`it` evaluator, the
same array literal is represented/passed differently at the point it
crosses that boundary — plausibly a raw interpreter-internal value
handle/index rather than a real heap pointer, which would be `< 4096` (or
otherwise fail the tag check) and get rejected by `rt_core_as_array`'s very
first guard, `if (raw < 4096) return NULL;`. That produces exactly the
observed symptom: no crash (the guard is a normal, deliberate null-check),
no error text (the caller treats `NULL` array as "empty input" and returns
a valid empty string rather than propagating a failure) — just silent data
loss.

This is a hypothesis, not a confirmed root cause: it was inferred by
reading `rt_core_as_array`'s guard clauses against the observed behavior,
not by attaching a debugger to the two argument-marshaling paths and
diffing the actual `int64_t` value each evaluator passes across the extern
boundary. That instrumented comparison (log the raw `bytes_value` seen
inside `rt_bytes_to_text` under `run` vs under `test`) is the fastest way
to confirm or refute it.

## Why this is probably the same root as the parallel "imported functions return EMPTY under `simple test`" reports

Both share: (1) no crash/error, only silent empty/nil results; (2) confined
to `bin/simple test` (SSpec) specifically, `bin/simple run` unaffected;
(3) the pattern is "correct data goes in, empty comes out" rather than
wrong-but-nonempty data, consistent with a guard clause in the runtime
rejecting a malformed handle rather than a logic error in the actual
conversion code. If the other lane's repro also involves an array-typed (or
otherwise heap-boxed, non-scalar) extern argument, this is very likely the
same defect; a scalar-only (`i64`/`bool`/`f64`) extern argument would not
hit `rt_core_as_array` at all and should not exhibit this. (A related, but
distinct, finding from the same investigation: scalar `i64` extern
arguments have their own gap — `rt_char_from_code(code: i64) -> text`, a
real runtime symbol, fails with `unknown extern function: rt_char_from_code`
under **both** `run` and `test`, i.e. missing interpreter registration
entirely rather than a marshaling mismatch. Different mechanism, same
"works under one path, not another" theme — noted here in case it's useful
triage context, not claimed to be the same bug.)

## What was ruled out

- **Not specific to `rt_bytes_to_text`'s conversion logic** — the same
  literal array, unmodified, produces correct output via `run`. The
  function body is not being executed differently; it is being handed a
  different (or empty) argument.
- **Not a general SSpec-vs-run divergence for all values** — plain
  scalar/text assertions and ASCII-only calls into the very same spec files
  that hit this bug pass identically under both evaluators (see
  `test/01_unit/lib/common/string_core_charcode_spec.spl` and
  `test/01_unit/lib/common/encoding/utf8_spec.spl`, where every ASCII and
  invalid-input-policy assertion — no array argument involved — is green
  under both `run` and `test`).
- **Not the nested-subprocess starvation bug** documented in
  `doc/08_tracking/bug/nested_run_subprocess_empty_stdout_under_test_2026-07-20.md`
  — that bug is about a *child process* (`rt_process_run` spawning a second,
  heavy `bin/simple run <app>/main.spl`) starving/failing under load.
  Observation 1 (this section) reproduces in-process, with no subprocess
  involved at all, on the minimal repro above. (Observation 2, next
  section, DOES involve a subprocess — see there for why it's still not a
  clean match for the starvation bug either.)

## Observation 2: a genuinely `exec`'d subprocess, still downstream of `bin/simple test`, still fails — mechanism NOT established

Found while building the subprocess-probe guard for the fix this doc
supports
(`test/03_system/interpreter/char_from_code_non_ascii_probe.spl` +
`char_from_code_non_ascii_system_spec.spl`, following the
`for_in_text_jit_probe.spl` / `for_in_text_jit_system_spec.spl` pattern of
spawning a plain, non-SSpec `fn main():` script via `rt_process_run` and
asserting on its stdout — precisely to route around observation 1 by using
a real `run` process instead of an in-process `it` block).

**Expected:** since the probe is a plain script with no `describe`/`it`
block anywhere in it, and the exact same probe run standalone (or nested
under a plain `bin/simple run` wrapper script) prints `ok` every time, the
subprocess spawned from inside the SSpec spec should also print `ok`.

**Actual:** it deterministically prints
`fail:code0 len expected=1 actual=0` instead — i.e. `char_from_code_inline(0)`
itself returned an empty string inside that subprocess, the same
`rt_bytes_to_text`-returns-empty signature as observation 1, but now
observed inside a script containing no SSpec constructs at all.

Confirmed:
- **Deterministic, not flaky**: reproduced repeatedly with the identical
  message every time.
- **Specific to the `bin/simple test` ancestor, not to nesting itself**:
  the identical probe, spawned via `rt_process_run` from a plain (non-SSpec)
  `bin/simple run wrapper.spl` parent instead, prints `ok` — nesting one
  `bin/simple run` inside another is NOT sufficient to reproduce this; the
  parent specifically has to be `bin/simple test`.
- **Not one of `bin/simple test`'s own self-set env vars leaking into the
  child**: `runner.rs` sets `SIMPLE_TEST_FILTER`, `SIMPLE_TEST_SHOW_TAGS`,
  and `SIMPLE_COVERAGE` for itself in various code paths. Running the probe
  standalone with each of `SIMPLE_COVERAGE=1`, `SIMPLE_TEST_FILTER=slow`,
  and `SIMPLE_TEST_SHOW_TAGS=1` set did **not** reproduce the failure — so
  it is not simply "one of these three flags happens to be set when `test`
  spawns children." This was a single timeboxed check of the three
  variables found by grepping for `set_var` in `test_runner/runner.rs`, not
  an exhaustive environment diff — a full `env` dump comparison between the
  two parent processes at the point they call `rt_process_run` is the
  logical next step and was not done here.

**Why this is NOT claimed to be the same mechanism as observation 1**: a
cleanly `exec`'d child process gets a fresh address space and, for a true
fork+exec, a fresh interpreter state — it cannot inherit an *in-process*
SSpec-evaluator marshaling quirk from its parent the way observation 1
describes. Something about being downstream of `bin/simple test`
specifically (not just downstream of another `bin/simple` process, and not
one of the three env vars checked above) changes this subprocess's own
behavior. That could still bottom out in the exact same
`rt_core_as_array`/tagged-pointer mechanism theorized for observation 1 (if,
for instance, `bin/simple test` primes some environment or on-disk cache
state that a spawned `bin/simple run` child then picks up and that changes
how *it* marshals arguments internally) — but that is speculation, not a
traced mechanism, and it is equally plausible these are two different bugs
that merely produce the same-shaped symptom because they both bottom out in
the same defensive `rt_core_as_array` guard clause for unrelated reasons.
**Do not merge this into observation 1's fix without independently
confirming the mechanism.**

**The important framing point for whoever picks up observation 2**: since
the failing process is a genuinely, cleanly `exec`'d child (no shared
address space, no shared interpreter instance with its parent), the
trigger CANNOT be an in-process interpreter-evaluator quirk. It has to be
something the child inherits or observes from its environment at
`exec`-time. `SIMPLE_COVERAGE` / `SIMPLE_TEST_FILTER` / `SIMPLE_TEST_SHOW_TAGS`
were checked and ruled out (see above), but that was three specific
variables, not an exhaustive comparison. Remaining, unchecked candidates,
roughly in order of how cheap they are to check:
- **Full env delta.** Have the probe itself dump its entire `env` (or read
  `/proc/self/environ` if there's no stdlib env-dump primitive handy) under
  all three parent contexts (standalone, nested-under-`run`,
  nested-under-`test`) and diff them. This is the most direct way to either
  confirm or rule out "environment" as a category in one pass, rather than
  guessing at variable names one at a time.
- **Working directory.** Confirm the child's actual `cwd` (e.g. via
  `pwd`/`getcwd`) is identical in the nested-under-`run` and
  nested-under-`test` cases — `rt_process_run`'s cwd-inheritance behavior
  was assumed, not directly verified, in this investigation.
- **stdin/stdout/stderr being a pipe vs. a tty**, and generally which file
  descriptors are open/inherited. `bin/simple test` necessarily captures
  its own stdout differently than an interactive shell does (it has to
  collect SSpec output for the summary report), and that could easily
  propagate to how it sets up a spawned child's descriptors even though
  `rt_process_run`'s own basic stdout-capture was independently confirmed
  to work (see "A basic subprocess+stdout-capture sanity check passes" in
  the sibling nested-subprocess doc referenced above) — that check used a
  trivial `/bin/sh -c` command, not a nested `bin/simple run`, so it does
  not rule this out for a nested Simple child specifically.
- **Inherited resource limits.** `bin/simple test` running a large,
  memory-heavy test suite could plausibly have adjusted (or hit) `ulimit`
  values (open file descriptors, memory, stack) that a spawned child then
  inherits, in a way that changes how the child's own runtime initializes
  or allocates the heap that backs `RtCoreArray`/`rt_core_as_array`.

A **full `env` dump diff** between the nested-under-`run` and
nested-under-`test` cases (first bullet above) is the single fastest way to
either name the trigger outright or eliminate "environment" as a category
entirely, and was not done in this investigation — recommended as the
actual next step, ahead of instrumenting the C runtime (below).

**Four-cell verification of the subprocess-probe guard that found this**
(`test/03_system/interpreter/char_from_code_non_ascii_probe.spl` +
`char_from_code_non_ascii_system_spec.spl`, guarding
`char_from_code_non_ascii_unsupported_2026-07-20.md`): with the fix's
source reverted (`char_from_code_inline` / `char_from_codepoint` restored
to their pre-fix, ASCII-only behavior) in a scratch worktree —
- fix present + `run` → `ok` (correct)
- fix present + `test` → tolerated (`gap:rt_bytes_to_text_env...`)
- fix **reverted** + `run` → `fail:code0 len expected=1 actual=0` (correctly
  RED — this is the real guard)
- fix **reverted** + `test` → tolerated (`gap:rt_bytes_to_text_env...`,
  same as fix-present) — the canary that produces this message runs BEFORE
  any of the reverted encoding logic, and is itself blocked by this
  observation-2 gap regardless of whether the fix is present or reverted,
  so this specific cell is unobservable through this probe until
  observation 2 itself is fixed. Documented plainly in the spec's own
  header comment rather than left implicit.

## Suggested next step for whoever picks this up

**Observation 1:** instrument `rt_bytes_to_text` (or `rt_core_as_array`) to
print/log the raw `int64_t bytes_value` it receives, then run the minimal
repro above under both `bin/simple run repro.spl` and
`bin/simple test repro_spec.spl` and diff the two logged values. That will
either confirm the tagged-pointer-vs-raw-handle hypothesis directly, or
point at the real divergence if it's something else entirely (e.g. a
different marshaling layer never reaching `rt_core_as_array` at all, in
which case the empty result would come from somewhere else in the call
chain and this doc's "entry point" section would need correcting).

**Observation 2:** same instrumentation, but compare three runs of the
`char_from_code_non_ascii_probe.spl` repro (or the even more minimal
`rt_bytes_to_text([65u8, 66u8])` repro, adapted to a subprocess): (a)
standalone, (b) nested under a plain `bin/simple run wrapper.spl`, (c)
nested under `bin/simple test spec.spl`. (a) and (b) are confirmed `ok`;
(c) is confirmed to fail. Diff the logged `bytes_value` between (b) and (c)
specifically — if they differ, that is direct evidence of *something*
`bin/simple test` does differently when spawning children (env, cwd, fd
inheritance, or an on-disk cache/lock file state); if they're identical
and the C-level behavior still differs, the divergence is happening above
`rt_bytes_to_text` entirely and this doc's C-level framing does not apply
to observation 2. Either result meaningfully narrows this down — right now
neither has been checked.
