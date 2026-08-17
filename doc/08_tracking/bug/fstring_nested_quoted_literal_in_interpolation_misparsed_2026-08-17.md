# f-string: a string literal on the RHS of `??` inside an interpolation is mis-parsed

(Filename says "nested quoted literal" — that was the initial, and wrong,
characterisation. The trigger is specifically the `??` right-hand side; see the
isolation table below. Filename kept stable so existing references still resolve.)

- **Filed:** 2026-08-17
- **Status:** OPEN (grammar defect unfixed); the one load-bearing call site is worked around
- **Severity:** P2 as a grammar defect. It was P1 in *effect*, because the single
  affected call site sits on `native-build`'s stderr-truncation path and its parse
  error was emitted **instead of** the real build diagnostic.

## Symptom

A string literal on the right-hand side of `??` inside an f-string interpolation is
mis-parsed. The scanner terminates that literal early, so its *contents* are then
read as an expression — a bare identifier, in call or variable position:

```
error[E1002]: function `TMPDIR` not found
  = help: check the function name or import the module that defines it
```

## The trigger is `??` with a string-literal RHS — NOT nested quotes generally

**Corrected after further isolation.** An earlier draft of this row blamed "a
nested double-quoted literal inside an interpolation". That is measurably WRONG
and would have misdirected the fix. Isolation, same binary:

| variant | source | rc | result |
|---|---|---|---|
| A | `"{pick("TMPDIR")}/x.log"` — nested literal as a call ARG, no `??` | **0** | PASSES, prints `p=TMPDIR/x.log` |
| B | `"{q ?? "/tmp"}/x.log"` — string literal as `??` RHS, no nested call | **1** | ``error: semantic: variable `tmp` not found`` |
| A+B | `"{pick("TMPDIR") ?? "/tmp"}/x.log"` | **1** | ``error[E1002]: function `TMPDIR` not found`` |

Variant A **passes**, so nested quoting inside an interpolation is fine on its
own. The necessary element is a **string literal on the right-hand side of `??`
inside an f-string interpolation**.

Variant B's error text pins the mechanism exactly: the reported missing name is
`tmp`, which is the *tail* of the literal `"/tmp"`. The scanner ends the literal
at the `"/` and then parses the remainder, `tmp`, as an identifier. When a nested
call argument is also present (A+B) the corrupted scan surfaces on the earlier
token instead, which is why the original symptom named `TMPDIR` rather than `tmp`
and sent this investigation toward the wrong hypothesis.

## Minimal repro — 6 lines, no imports

```simple
fn pick(a: text) -> text:
    a

fn main() -> i64:
    val p = "{pick("TMPDIR") ?? "/tmp"}/x.log"
    print("p={p}\n")
    0
```

Measured with `bin/simple run` on the Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, size 59537240,
mtime 2026-08-17 12:58:51 UTC, md5 `78ffcbcd3f4cfaa11e3d9c1db37bf0b2`):

| arm | source form | rc | output |
|---|---|---|---|
| reverted | `"{pick("TMPDIR") ?? "/tmp"}/x.log"` | **1** | ``error[E1002]: function `TMPDIR` not found`` |
| applied | hoisted: `val root = pick("TMPDIR") ?? "/tmp"` then `"{root}/x.log"` | **0** | `p=TMPDIR/x.log` |

Both arms ran on the **same** binary — the ablation is over SOURCE, so there is
no possibility of the two arms being the same mislabeled build.

## Why this mattered out of proportion to its size

`src/app/cli/native_build_main.spl:226` used exactly this form to build the
spill-log path on the branch that runs when worker stderr exceeds
`OUTPUT_LIMIT`. Consequence: whenever `native-build` had *enough* diagnostic
output to truncate, the file on that path failed to compile, and the emitted
error was ``function `TMPDIR` not found`` rather than the actual build failure.
This is the same class of defect as the swallowed-`diagnostics` finding in
`native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md`:
the error-reporting path destroying the evidence for the error it was reporting.

Note the diagnostic is followed by a trailing `= help:` line, so the verdict/error
is **not** the last line of stdout — `tail -1` reads the wrong line here.

## Census

`grep -rn '"{[a-z_]*(\"' src/app src/compiler src/lib` finds exactly **two**
sites repo-wide:

- `src/app/cli/native_build_main.spl:226` — **worked around** (hoisted to a local,
  with a comment pointing here). This is the load-bearing one.
- `src/lib/nogc_sync_mut/debug_doctor/matrix.spl:335` —
  `"{_pad("target", target_w)}  {_pad("attach", attach_w)}  ..."`. **VERIFIED
  UNAFFECTED** — reproduced as a standalone fixture, rc=**0**, prints
  `target  attach  profile`. It has nested literals but no `??`, i.e. it is
  variant A above. Correctly left untouched: it was never broken.

So after the fix there are **zero** affected sites in tree, and the grammar defect
has **no** surviving in-tree reproducer. The 6-line fixture in this row is the
reproducer; a regression spec should be added when the grammar is fixed.

## Real fix (not done here)

The workaround normalises the call site; per the repo rule against silently
normalising a failing short form, the grammar itself is the defect and is
recorded here rather than treated as closed.

The fix belongs in the f-string interpolation scanner, and the isolation above
narrows *where*: literals as call arguments are already consumed correctly
(variant A passes), so the naive-scan-to-next-quote theory cannot be the whole
story. What fails is the literal after the `??` operator. The likely shape is that
the interpolation's expression scanner has a special path for `??` — or stops
tracking quote state once it has seen an operator at that precedence — and hands
the RHS to a scan that terminates the literal at `"/`. Anyone fixing this should
start by finding why the `??` RHS position is scanned differently from an argument
position, rather than rewriting the whole interpolation scanner.

Regression coverage to add with the fix: all three variants above, since a fix
that only repairs A+B while leaving bare B broken would look green on the original
symptom.

## Not related to the receiver-erasure hypothesis

This defect was found while chasing
``method `compile` not found on type `object` `` in the native lane. They are
**not** the same thing, and that hypothesis is separately refuted — see
`doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`.
