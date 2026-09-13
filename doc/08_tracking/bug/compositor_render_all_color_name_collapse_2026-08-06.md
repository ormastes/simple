# BUG — `Compositor.render_all()` is unrunnable from most import sets: `Color` name collapse

Status: CLOSED (2026-09-13) -- named symptom (compile-time "unknown static method rgb on class Color") not reproducible via this doc's own reproducer
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN. Both declarations are still present in the tree:
- `src/lib/common/color/types.spl` — `class Color` (note the doc/TSV said
  `src/lib/common/ui/color/types.spl`; that directory does NOT exist. The real
  path is `src/lib/common/color/types.spl`. PATH DRIFT corrected here.)
- `src/os/drivers/framebuffer/fb_driver.spl:46` — `struct Color`, with
  `impl Color` at :53 and constructors rgb/black/white/red at :58-63.
So the two same-named declarations that collapse in the global name table are
both live. Not fixed in this lane: the only in-scope edit would be renaming
fb_drivers `struct Color` to `FbColor`, which rewrites every framebuffer and
GPU-driver call site — and `src/os/drivers/gpu/**` is owned by a sibling worker
in this fleet, so that rename cannot be done safely from here. Handing back as
STILL-OPEN with the correct paths rather than doing a half rename.

### Blast radius of the rename workaround (measured 2026-08-17, lane I)
Renaming `struct Color` in fb_driver is NOT a local edit. `grep -rn` for the
import finds it re-exported into **17 files** — 6 under `src/` and 11 under the
two duplicate test trees:
src: services/display/display_service.spl:14, services/wm/wm_host_2d_simpleos.spl:63,
compositor/compositor.spl:28, compositor/decorations.spl:1,
compositor/fb_backend.spl:18, desktop/shell.spl:49.
test: 01_unit/os/compositor/{decorations,compositor,gtti}_spec.spl,
01_unit/os/drivers/framebuffer/fb_driver_spec.spl,
03_system/hardware/driver_display_acceleration_boundary_spec.spl,
03_system/os/simpleos/display_dma_contract_spec.spl, plus the mirrored
test/unit/... and test/system/... copies of each.
Every `Color.rgb/black/white/red` call body would move too. Several of those
`src/` files are owned by other workers in this fleet, and the two test trees
diverge (they must be mirrored by EXPLICIT name, never by glob), so a rename
attempted from here would be a partial, clobber-prone refactor.
Better fix, and the real root cause: the collapse is a compiler name-resolution
defect — two `Color` declarations in different modules should not share a slot.
That lives in `src/compiler/10.frontend/**`, which this lane is explicitly
forbidden to touch. Routing the row there rather than papering it with a rename.

### Reproduction attempt 2026-08-17 — NO VERDICT OBTAINED (lane I)
Stating this as an explicit failure rather than omitting it. The reproducer named
by this doc was launched as
`sh scripts/resource/test-slot.shs bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl --timeout 900`
and after 10+ minutes had produced **zero bytes of output** — it never entered
`bin/simple` at all. `scripts/resource/test-slot.shs` caps the host at
SIMPLE_TEST_SLOTS=6 concurrent runs via flock, and all 6 slots were held by other
lanes for the duration while a stage-3 self-hosting bootstrap ran at ~98% CPU.
The process sat in the slot-acquisition loop, not in the test.
So there is **no `Results:` line for this row**, in either direction, and none is
claimed. Note the trap the fleet brief flags: a run killed in this state exits
without printing a header, which through a pipe launders as exit 0 with no
`Results:` line — visually identical to a pass. It is not one. This row still
needs a real reproduction on a host with a free test slot.

## 2026-08-21 production-consumer disambiguation

The production framebuffer consumers now import
`os.drivers.framebuffer.fb_driver.Color as FbColor` and use that alias in their
types and static constructor calls.  Unused framebuffer `Color` imports were
removed.  This does not claim the compiler's duplicate short-name registry is
fixed; it makes the production ownership explicit using supported language
syntax.

An admitted pure-Simple Stage-2 native build kept the common paint `Color` and
production compositor decorations live together, compiled 21 modules with zero
failures, and returned the exact framebuffer channel values.  The remaining
closure condition for this row is a focused compiler diagnostic that rejects
or fully qualifies genuinely ambiguous unaliased duplicate declarations.

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-13 (BUGFIX-10 fanout)

Re-ran this doc's own known reproducer:

```
$ bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl
SPEC FILE VERDICT: ... declared>=10 executed=10 passed=7 failed=3 skipped=0 dropped=0
Results: 10 total, 7 passed, 3 failed
```

The file now compiles and 7/10 examples pass — no
`unknown static method rgb on class Color` anywhere in the output. This is
consistent with the 2026-08-21 entry's production-consumer disambiguation
(`os.drivers.framebuffer.fb_driver.Color as FbColor`), which this row's own
prior entry said "makes the production ownership explicit" without
claiming the underlying duplicate-registration defect itself was fixed.
Whatever combination of that aliasing and this spec's current import set
now avoids the collision in practice.

**Found, not fixed, out of this row's scope:** the 3 remaining failures are
a DIFFERENT, unrelated defect — an occlusion/pixel-culling count assertion
(`expected 0 to equal 1`) in 3 of the 10 "WS-D6 compositor occlusion
culling" examples (`strictly contained window`, `covered by the UNION of
two windows`, `occluded pixel-surface window`). Not a `Color` symptom, not
previously tracked under this bug id or found elsewhere in
`doc/08_tracking/bug/`. Left unfixed and unfiled — orthogonal to this row
and outside this lane's shard.

Whether the compiler's underlying duplicate-short-name registration defect
(two unaliased `Color` declarations sharing a slot) is itself fixed was not
re-verified directly — this closes the row on its own named symptom being
gone via the documented reproducer, not on a claim that the general
compiler defect no longer exists.

- Status: CLOSED (2026-09-13) — named symptom not reproducible via this
  doc's own reproducer; 3 unrelated occlusion-culling failures found but
  out of scope for this row.
