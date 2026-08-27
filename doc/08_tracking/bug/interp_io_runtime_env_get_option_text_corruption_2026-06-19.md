# std.io_runtime.env_get returns corrupted text under `bin/simple run`

Date: 2026-06-19
Status: open (workaround in place)
Severity: P2
Related: memory note "f64 Unreliable All Backends", "Text-only API byte cliffs"

## Symptom

`std.io_runtime.env_get(key)` (which wraps `extern fn rt_env_get(key: text) -> text`
and is consumed in apps as `env_get(key) ?? ""`) returns a corrupted `text` value
when run via `bin/simple run` (interpreter path). The returned text reports
`len() == -1` and interpolating it into a `print` collapses the whole formatted
line to blank. The raw extern `rt_env_get` returns the correct value.

This silently defeats env-var configuration: a `?? ""` default makes the caller
fall through to the fallback as if the variable were unset, even when it is set.

## Minimal repro (verified 2026-06-19)

A file under `examples/` (so module resolution finds `std`):

```simple
use std.io_runtime.{env_get}

fn main() -> i64:
    val v = env_get("FOO") ?? "<none>"
    print "len={v.len()}"            # prints: len=-1   (when FOO is set)
    print "FOO=[{v}]"                # prints a BLANK line, not FOO=[bar]
    return 0
```

Run: `FOO=bar SIMPLE_LIB=src bin/simple run examples/06_io/ui/_repro.spl`

Observed:
```
len=-1
<blank line>
```

## Contrast: the raw extern is correct

```simple
extern fn rt_env_get(key: text) -> text

fn main() -> i64:
    val v = rt_env_get("FOO")
    print "len={v.len()}"            # prints: len=3
    if v == "bar":
        print "matched"             # prints: matched
    return 0
```

Observed:
```
len=3
matched
```

So the defect is in the `std.io_runtime.env_get` wrapper / `text?` Option lowering
path, NOT in `rt_env_get` itself. The corruption surfaces specifically when the
`text` extern result is wrapped/unwrapped through the Option (`?? ""`) chain in
the interpreter `run` path.

## Workaround

Call `extern fn rt_env_get(key: text) -> text` directly and compare against `""`.
In use at `examples/06_io/ui/showcase_8k_scroll_gui.spl` (`env_i32` helper).

2026-06-21 update: replacing the 8K showcase helper with imported facade calls
was still unsafe. `use app.io.env_ops.{env_get as showcase_env_get}` made the
default run report a JIT unresolved-symbol fallback for `showcase_env_get`.
Using an unaliased facade import avoided that fallback, but
`SHOWCASE_8K_W=64 SHOWCASE_8K_H=64 SHOWCASE_8K_OFF_FRAMES=1
SHOWCASE_8K_ON_FRAMES=1 ... run examples/06_io/ui/showcase_8k_scroll_gui.spl`
still rendered the default `1280x800` surface and timed out. The same happened
with `std.nogc_sync_mut.io.env_ops.env_get`. Keeping a single local
`showcase_env_get()` wrapper around raw `rt_env_get` preserved the env values,
reported `64x64`, and completed without a JIT fallback line. This keeps the
runtime boundary localized but leaves the facade/import behavior open.

## Notes

- The existing showcase apps that read `env_get(...) ?? ""` and only test for
  `!= ""` (e.g. `SHOWCASE_PPM`, `SIMPLE_GUI`) appear to "work" because they never
  call `.len()` or interpolate the value — but if the variable is set, the `!= ""`
  branch may still misbehave for the same reason; not yet re-audited.
