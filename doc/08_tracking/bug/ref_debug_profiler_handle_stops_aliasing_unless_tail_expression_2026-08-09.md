# A capability handle stops aliasing its target unless the acquisition is a function's TAIL expression

> **DID NOT REPRODUCE 2026-08-17.** `test/01_unit/lib/debug/debug_target_ref_spec.spl`:
> `SPEC FILE VERDICT: declared>=71 executed=71 passed=71 failed=0 dropped=0` /
> `Results: 71 total, 71 passed, 0 failed`. Not vacuous — 71 examples executed.
> Binary `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
> 2026-08-16 22:59:37. Candidate for close.


- **Filed:** 2026-08-09 (stream P10, Lab debug/profile endpoints)
- **Status:** OPEN — worked around in `src/app/simple_lab/lab_debug.spl`
- **Severity:** high. Silent, partial, and produces wrong answers with no diagnostic.
- **Engine:** interpreter (`SIMPLE_EXECUTION_MODE=interpreter`), seed binary
  `bin/release/x86_64-unknown-linux-gnu/simple` (`Simple Language v1.0.0-beta`).

## Symptom

`ref_debug_profiler(session)` (P2, `src/lib/common/debug/ref_debug_session.spl`)
returns the one `DebugProfiler` value carrying both capabilities. Store that
handle in a container and only *some* of its mutations survive:

| operation | mutates | survives? |
|---|---|---|
| `step()` / `resume()` | `self.vm` (a class-typed **sub-object**) | **yes** |
| `set_breakpoint(loc)` | `self.breaks` (the target's own array field) | **no** |
| `profile_begin()` | `self.profile_armed` (own bool field) | **no** |

The partial survival is what makes this dangerous. Stepping looks perfectly
correct — pc advances, the stack grows — while breakpoints never arm
(`set_breakpoint` returns `true` every time, `breakpoints()` stays `[]`, and
`resume` runs straight past) and every profile window comes back
`level=unavailable, detail=reason=profile_end-without-profile_begin`. A reader
sees an honest-looking "profiling unavailable" report and has no reason to
suspect the harness rather than the target.

## What actually decides it

Not the container. Measured with a matrix of shapes, all with the same
`RefDebugTarget`:

| shape | breakpoint survives? |
|---|---|
| bare local (`var a = mk()`) | yes |
| struct field (`SBox(dp: mk())`) | yes |
| class field (`CBox(dp: mk())`) | yes |
| `[DebugProfiler]` inside a class, mutated via a `me` method | yes |
| **acquisition bound to a local in the same frame that built `session`** | **no** |
| acquisition inlined into a constructor in that same frame | **no** |
| acquisition returned inside a struct from a free fn | **no** |
| acquisition as the free fn's **tail expression** | yes |

`mk()` (works) and the broken variants differ only in *where the acquisition
call sits*:

```simple
fn mk() -> DebugProfiler:
    var s = RefDebugSession.new()
    val d = s.attach(PROG, opts)
    ref_debug_profiler(s)          # TAIL -> handle stays live

# vs, all three broken:
val acquired = ref_debug_profiler(session)      # bound in session's frame
Entry(dp: ref_debug_profiler(session))          # inlined in session's frame
Acq(ok: true, dp: ref_debug_profiler(session))  # returned inside a struct
```

So the rule is about the acquisition's syntactic position relative to the frame
holding `session`, not about the destination. Writing the copy back afterwards
(`entry.dp = target; self.entries[i] = entry`) does **not** repair it — that was
tried first and is a red herring.

A neighbouring data point from the same probe: reading the concrete field
directly, `session.target.set_breakpoint(15)`, loses the mutation too. So
`Option<RefDebugTarget>` field reads share the defect; it is not specific to
trait-typed storage.

## Reproduction

The isolating probe is not checked in (it was a scratch file). To rebuild it:
construct `RefDebugSession`, `attach` the P2 vector
`"PUSHI 1\nPUSHI 3\nPUSHI 4\nADD\nSYS_RESULT\nHALT 0"`, acquire via
`ref_debug_profiler`, then compare `set_breakpoint(15)` / `breakpoints()`
across the shapes in the table above.

## Why P2's own spec is green

`test/01_unit/lib/debug/debug_target_ref_spec.spl` holds the handle in ONE
local for the life of each example and never routes it through a container
built in the same frame — exactly the shape that works. The trait contract is
correct; only handles that cross a frame boundary the wrong way are affected.

## Workaround in force

`src/app/simple_lab/lab_debug.spl` splits attach into two functions so the
acquisition is a tail expression:

- `_lab_ref_attach_diag(source, budget, profile) -> text` — a probe attach used
  only to obtain the three-way `"" / "skip:" / "error: "` diagnostic. Its
  session is discarded.
- `_lab_ref_acquire(source, budget, profile) -> DebugProfiler` — attaches again
  and *returns* the acquisition as its tail.

The cost is one redundant attach per lane (assembling a small SVM-G program;
negligible here, but it would not be on a lane that uploads to a device). When
this defect is fixed the two collapse back into one function and the comment
block at the top of `lab_debug.spl` (value-semantics rule 2) should be deleted
with them.

## Impact beyond P10

Any stream that stores a `DebugTarget`/`ProfileTarget`/`DebugProfiler` handle in
a registry — P3 (host target), P6 (CUDA/Vulkan sessions), P9 (DAP target
session) — will hit this the moment it acquires into a local before storing.
The failure will look like "breakpoints do not work on this backend" or
"profiling is unavailable on this backend", i.e. it will be misread as a
backend gap rather than a harness defect.

## Related

- `doc/08_tracking/bug/capability_group_from_unsound_under_value_semantics_2026-08-09.md`
  — the P2 defect this is adjacent to but distinct from. That one is about
  PAIRING two accessors; this one bites a single accessor used correctly.
