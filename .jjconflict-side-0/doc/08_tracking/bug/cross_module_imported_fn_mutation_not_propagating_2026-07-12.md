# Cross-module imported function mutation not propagating to caller's instance

## Status

Open. Workaround applied in `graphics_2d_showcase_gui.spl` (local, RENAMED copies of
`draw_showcase`/`label` — `wm_draw_showcase`/`wm_label` — plus unmodified helpers/constants)
— see comment block there for removal instructions once fixed.

**Verified 2026-07-12:** a plain verbatim local copy (same names as the source module)
was NOT sufficient — it still produced a blank frame (0/1,440,000 nonzero bytes). The
module also imports `graphics_2d_showcase.{run_graphics_2d_showcase}` (needed by the
standalone non-client `main()` branch), and that import leaks the source module's own
`draw_showcase`/`label` symbols into scope. Local definitions sharing those exact names
lost the name-resolution race to the leaked (copy-mutating) originals — i.e. calling
`draw_showcase(engine)` silently resolved to the *imported* module's version, not the
local one, reproducing the identical blank-frame symptom. Renaming only the two
`e`-mutating local functions (`draw_showcase`→`wm_draw_showcase`, `label`→`wm_label`)
and updating call sites fixed it: 1,439,967/1,440,000 nonzero bytes. The non-mutating
helpers (`checker_pixels`, `showcase_mask`) and the color constants were left unrenamed
since they are return-only / identical-valued and the collision is harmless there — but
prefixing everything copied is the safer general practice.

## Symptom

A function imported cross-module that takes a class instance parameter (e.g. `e: Engine2D`)
and mutates it in place (via `e.clear(...)`, `e.draw_rect_filled(...)`, etc.) does not
propagate those mutations back to the caller's instance. The caller's instance is left
unmodified, so a subsequent readback of that instance is all-zero/blank.

## Evidence

- `examples/06_io/ui/graphics_2d_showcase_gui.spl` `run_wm_client_graphics_2d()`
  (around line 27-33, prior to the workaround) called
  `draw_showcase(engine)` where `draw_showcase` was imported via
  `use graphics_2d_showcase.{run_graphics_2d_showcase, draw_showcase}`
  (sibling-relative cross-module import — see the file's header comment on why
  the sibling form is used instead of `examples.ui.graphics_2d_showcase`).
  After `draw_showcase(engine)` + `engine.present()`, `engine.read_pixels_with_source().pixels`
  was all-zero (0 of 1,440,000 nonzero bytes) — a blank 800x600 PPM.
- A same-module control test on the identical `engine` object —
  `engine.clear(0xFF00FF00)` called directly in `graphics_2d_showcase_gui.spl`
  (not through the cross-module import) — DID mutate the instance correctly
  (480000/480000 nonzero on the relevant channel).
- The standalone `examples/06_io/ui/graphics_2d_showcase.spl`, which defines
  `draw_showcase` AND calls it in the SAME module (`run_graphics_2d_showcase()`,
  line 163), renders correctly: 479989/480000 nonzero pixels.
- An earlier version of the WM client that copied `draw_showcase` verbatim into
  its own module (instead of importing it) also rendered nonblank, confirming
  the mutation-propagation break is specific to the cross-module import path,
  not to `draw_showcase`'s logic or to `Engine2D` itself.

## Suspected cause (confirmed mechanism, root cause still open)

Isolated testing (2026-07-12, see Evidence) confirmed the actual mechanism is
**name-resolution shadowing at the `use module.{specific_names}` boundary**,
not a value-copy/ABI issue:

- A locally-defined function (in the importing module) that has the SAME NAME
  as a function defined in the imported module — even when that name is NOT
  in the explicit `{...}` import list — loses the name-resolution race to the
  imported module's version when called. The call site silently resolves to
  the *other* module's (copy-mutating, per the original symptom) function
  instead of the local one in scope.
- This was proven by: (a) a verbatim local copy of `draw_showcase`/`label`
  in `graphics_2d_showcase_gui.spl`, which ALSO imports
  `graphics_2d_showcase.{run_graphics_2d_showcase}`, still produced a blank
  frame (0/1,440,000 nonzero); (b) an isolated reproduction outside the WM/GUI
  plumbing (identical copied `draw_showcase` + helpers, called directly from
  `main()`, with NO import of the sibling `graphics_2d_showcase` module)
  rendered correctly (479989/480000 nonzero); (c) renaming only the two
  colliding, `e`-mutating local functions (`draw_showcase`→`wm_draw_showcase`,
  `label`→`wm_label`) while keeping the `run_graphics_2d_showcase` import
  fixed the blank-frame symptom (1,439,967/1,440,000 nonzero).

This still leaves the underlying compiler root cause open: why does a `use
module.{A}` import (explicitly naming only `A`) leak/shadow other same-named
top-level symbols (`draw_showcase`, `label`) from that module into the
importing module's resolution scope, and why does the leaked symbol win over
a same-named local definition? This needs a compiler-side repro isolated from
the WM/GUI plumbing to pin down whether it's import-list scoping (`{...}`
should exclude non-listed names entirely) or a resolution-order bug (locally
defined names should always shadow imported ones on a name collision).

## Impact

The host-WM `graphics_2d_showcase_gui.spl` client render path produced a blank
800x600 frame whenever `draw_showcase` was called through the cross-module
import. Any similar cross-module pattern (import a mutating function taking a
class instance, call it on a caller-owned instance, expect in-place mutation)
is presumed affected until root-caused.

## Workaround

Copy the mutating function (and every helper/constant it depends on) into the
caller's module instead of importing it cross-module — AND rename any copied
symbol that shares a name with something defined in a module you still import
from (a verbatim-name copy is NOT sufficient if that other module remains
imported, even partially via `{specific_names}` — see mechanism above).

Applied in `examples/06_io/ui/graphics_2d_showcase_gui.spl`: `draw_showcase`
and `label` are copied in and renamed to `wm_draw_showcase`/`wm_label` (both
mutate the `Engine2D` receiver and both collide with `graphics_2d_showcase`'s
own same-named functions); `checker_pixels`, `showcase_mask`, and the color
constants (`BG`, `PANEL`, `WHITE`, `BLUE`, `CYAN`, `GREEN`, `AMBER`, `RED`,
`PURPLE`) are copied in unrenamed (return-only / identical-valued, so the
collision is harmless there, though prefixing everything is the safer general
practice). Only `run_graphics_2d_showcase` remains imported from
`graphics_2d_showcase` (used solely by the standalone non-client `main()`
branch).

## Acceptance

- Root cause identified: duplicate type/module registration vs. value-copy
  ABI issue across sibling-relative cross-module imports.
- A minimal compiler-level repro (two modules, mutating function + instance,
  no WM/GUI dependencies) reproduces and then passes after the fix.
- `graphics_2d_showcase_gui.spl`'s local copy of `draw_showcase` and helpers is
  deleted and the cross-module import restored, and the client render path
  still produces a nonblank frame.
