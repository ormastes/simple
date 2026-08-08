# BUG — `Compositor.render_all()` is unrunnable from most import sets: `Color` name collapse

**Filed:** 2026-08-06 (WS-D6) · **Status:** OPEN · **Pre-existing:** yes, reproduced at HEAD
**Binary:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `ed53cc5f255e269ca27c4cd83b17aef9` (Rust seed build).

## Symptom

```
error: semantic: unknown static method rgb on class Color
```

No `-->` file:line is attached, which is a second defect: the diagnostic names
neither the call site nor the two colliding declarations, so the failure has to
be bisected by import set.

## Reproduction

A program that imports `os.compositor.compositor.{Compositor}` and
`os.compositor.display_backend.{CompositorBackend}` and actually *calls*
`Compositor.render_all()` fails to compile. Importing the same modules without
calling `render_all()` compiles fine ("imports ok"), so this is triggered by
what the render path pulls in, not by the import statement.

## Root cause

Two unrelated `Color` types are co-compiled and the first registration wins
(the documented same-name-collapse behaviour, cf. the `MouseEvent` note in
`src/os/compositor/compositor.spl:5-13`):

| declaration | fields | has `static fn rgb` |
|---|---|---|
| `src/lib/common/color/types.spl:3` `pub class Color` | `r,g,b,a: i64` | **no** |
| `src/os/drivers/framebuffer/fb_driver.spl:38` `struct Color` | `r,g,b,a: u8` | yes (`:50`) |

`src/os/compositor/decorations.spl:1` imports the fb_driver `Color` and calls
`Color.rgb(...)` at `:51,54,57,63,66`. When the common `Color` registers first,
those calls resolve against a class that has no `rgb`.

Because the two share field names `r,g,b,a`, a "fix" that rewrites
`Color.rgb(50,50,50)` into `Color(r: 50, g: 50, b: 50, a: 255)` **compiles while
constructing the wrong type** (i64 fields, not the u8 ARGB struct). That is a
cover-up, not a fix — do not take it.

## Why this matters

It is why `Compositor.render_all()` had no execution coverage: any spec that
drives it dies at semantic analysis unless it happens to pull in a module set
that registers the fb_driver `Color` first.

## Known-good workaround (used, not a fix)

`test/fixtures/wm_compositor_content_kind_render_probe.spl`'s exact import set
does resolve. `test/01_unit/os/compositor/compositor_occlusion_spec.spl` copies
it verbatim for that reason and says so in its header. This is fragile: any
import edit to that spec can resurrect the error.

Additionally, the resolution is **sensitive to the file's location** — the same
source under `/tmp` fails where the identical file under `test/fixtures/`
succeeds. That points at module-root discovery, and is worth a separate look.

## Fix direction (out of WS-D6 file scope)

Rename one of the two declarations. `src/lib/common/color/types.spl` is the
newer, browser-paint-oriented one and is the better rename candidate
(e.g. `PaintColor`); `src/os/drivers/framebuffer/fb_driver.spl` is under
`src/os/drivers/**`. Either way the compiler should **reject** duplicate
type registrations rather than silently keeping the first.
