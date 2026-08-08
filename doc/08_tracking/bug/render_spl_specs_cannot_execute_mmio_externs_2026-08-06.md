# `src/os/gui/render.spl` is unexecutable in-tree — its only spec has never run an assertion

- **Filed:** 2026-08-06
- **Status:** Open
- **Severity:** Medium — a vacuous coverage claim, not a wrong answer
- **Component:** os/gui/render + test harness
- **Found by:** WS-F4 presentation-path audit

## Symptom

Every entry point in `src/os/gui/render.spl` reaches `rt_mmio_read_u32` /
`rt_mmio_write_u32`, which are **baremetal-image externs with no host
definition**. Loading the module in this tree fails semantic analysis:

```
error: semantic: unknown extern function: rt_mmio_write_u32
```

## Measured, both engines

Rust bootstrap seed `bin/release/x86_64-unknown-linux-gnu/simple`, md5
`ed53cc5f255e269ca27c4cd83b17aef9`:

| what | verdict |
|---|---|
| `bin/simple test test/01_unit/os/render_pixel_bridge_spec.spl` | `2 total, 0 passed, 2 failed` — **pre-existing** |
| `bin/simple test test/01_unit/os/render_blit_from_addr_spec.spl` | `5 total, 0 passed, 5 failed` |
| `bin/simple run <equivalent probe>` | same error after `[jit-fallback] ... dropped to the interpreter` |

Both engines, same cause. This is not a JIT/interpreter divergence.

## Why it matters

`render_pixel_bridge_spec.spl:1` declares:

```
# @cover src/os/gui/render.spl 70%
```

That spec has **never executed a single assertion in this tree**. The coverage
header asserts 70% of a file whose every code path is unreachable here, so any
tooling that consumes `@cover` is being told this module is well covered when
it is not covered at all. The spec is not wrong — it would be correct inside a
baremetal image — it is simply *inert*, and nothing surfaces that.

This is the `painted=N` shape again: a signal that looks like evidence of
execution but only records that something was declared.

## Consequence for changes to this file

Any change to `src/os/gui/render.spl` or its callers is **unverifiable by spec
in this tree**. It can be reviewed, and it can be reasoned about, but it cannot
be measured until either:

- a baremetal image is buildable here (blocked: `bin/simple` is the Rust seed
  and the attested guest build exits `compiler-version-invalid`), or
- host stubs for `rt_mmio_read_u32` / `rt_mmio_write_u32` exist so the shadow
  buffer path can run headless.

The second is the cheap fix and is worth doing: the shadow buffer is plain RAM,
`g_fb_addr == 0` already makes `render_present()` a no-op, and the module is
explicitly designed so "a headless caller/test can assert the shadow buffer
contents via px_read" (`render.spl:193-194`). That design intent is currently
unrealisable because the two externs it rests on are absent.

## Suggested fix

Provide host definitions of `rt_mmio_read_u32` / `rt_mmio_write_u32` as plain
loads/stores for the test runtime. They already "work on RAM and MMIO" per the
module header, so a host build needs nothing MMIO-specific. Then both specs run
as written, with no change to either.

## Related

- `test/01_unit/os/render_blit_from_addr_spec.spl` — carries the same blocker
  in its header so a future reader is not misled by a red verdict.
- `doc/09_report/render_pipeline_profile_2026-08-06.md` — Finding 2, the
  per-pixel readback this lane's change addresses.
