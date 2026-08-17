# f-string: a nested double-quoted literal inside an interpolation is mis-parsed

- **Filed:** 2026-08-17
- **Status:** OPEN (grammar defect unfixed); the one load-bearing call site is worked around
- **Severity:** P2 as a grammar defect. It was P1 in *effect*, because the single
  affected call site sits on `native-build`'s stderr-truncation path and its parse
  error was emitted **instead of** the real build diagnostic.

## Symptom

A double-quoted string literal nested inside an f-string interpolation is
mis-parsed. The interpolation scanner terminates the inner literal early, so the
literal's *contents* are then read as an expression — a bare identifier in call
position:

```
error[E1002]: function `TMPDIR` not found
  = help: check the function name or import the module that defines it
```

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
  `"{_pad("target", target_w)}  {_pad("attach", attach_w)}  ..."`. **NOT yet
  verified** to fail; it is left untouched deliberately so a real repro of the
  grammar defect survives in-tree. Whoever fixes the grammar should check it.

## Real fix (not done here)

The workaround normalises the call site; per the repo rule against silently
normalising a failing short form, the grammar itself is the defect and is
recorded here rather than treated as closed. The fix belongs in the f-string
interpolation scanner: when scanning an interpolation, string literals inside the
braces must be consumed as literals, with brace/quote nesting tracked, instead of
the interpolation being delimited by a naive scan to the next `"` or `}`.

## Not related to the receiver-erasure hypothesis

This defect was found while chasing
``method `compile` not found on type `object` `` in the native lane. They are
**not** the same thing, and that hypothesis is separately refuted — see
`doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`.
