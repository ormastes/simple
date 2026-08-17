# macOS Vulkan 2D vector-font empty-batch native fault

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Scope

The manifest-attested macOS Vulkan 2D binary built successfully at pushed
revision `24345dfc8c83` (207/207 modules, zero compile failures). The live
wrapper re-admitted the trusted manifest after the report-order fix, launched
the exact binary, and then failed closed because the process exited before
publishing its ready or runtime receipt.

## Reproduced evidence

- Live result: `launched-process-missing`.
- Exact process stderr: `runtime error: field access on nil receiver`.
- A direct run of the same trusted binary also printed the nil-receiver error
  before producing a receipt. The retained diagnostic does not bind a signal
  exit code.
- A minimal native Vulkan diagnostic reached backend creation, font loading,
  selected Bungee identity, two `draw_text` calls, and renderer installation;
  those calls recorded zero rasterizations.
- `Engine2D.font_execution_attempts()` and
  `Engine2D.font_execution_target()` are declared with `fn` while reading
  `self`; changing them to receiver methods (`me`) removes that nil-receiver
  trap.
- One native diagnostic recorded `engine.font_owner.active.len() == 1` and
  then trapped while accessing the element receiver. In a separate run,
  `engine.fonts()` returned a renderer with the selected TTF identity.
- Routing the selected Vulkan backend as the concrete default font execution
  target entered canonical vector staging, but emitted:

  ```text
  [font-batch] degenerate source=text content=6 quads=0 atlas_pixels=1048576 \
  identity=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static \
  generation=1
  ```

  The retained output did not reach the post-cold-draw marker.

### 2026-07-27 bounded no-bootstrap diagnostics

Three focused current-source native-build cycles were run without bootstrapping:

- Cycle 1 compiled 185 modules with zero compile failures in approximately
  9.9 seconds, but the diagnostic process produced empty standard output.
- Cycle 2 compiled 184 modules in 10.2 seconds. Its entry and receipt sentinels
  succeeded and it selected the exact Bungee face at a computed 100 px size.
  However, the layout, raster, local, inbound, staged, stage-return, and alpha
  scalar checkpoints all serialized as empty values.
- In the same cycle, `post_engine_fonts` and `post_install_retrieve` serialized
  as the nil sentinel `2305843009213693951` (`0x1fffffffffffffff`).
- The third and final bounded cycle started from
  `bb9a9b60edcc572e86555e8c929bfabc20b74a62`. Its scalar-only diagnostic
  explicitly initialized every checkpoint and exposed individual `i64`
  getters directly from the live `Engine2D` font owner. The no-bootstrap
  native build compiled 184 modules with zero failures and linked a 654 KB
  binary with SHA-256
  `8460a54790068788b5c4997b59ad0d04ed73e863f5d281a48f7d34a7f3f1164a`.
  The run exited 132 with `runtime error: field access on nil receiver` before
  producing any checkpoint output.
- All third-cycle diagnostic source and probe edits were reverted after that
  failure. The three-cycle cap is exhausted: no retry, bootstrap, renderer
  change, or Vulkan live gate is permitted in this session.

These facts are summarized here because the diagnostic directory
`/private/tmp/simple-font-zero-quads-evidence-448d2a5` is ephemeral. It is not
a retained, manifest-bound evidence artifact and must not be cited as live
acceptance provenance.

The third-cycle binary is an ephemeral diagnostic product. Its hash identifies
the exact failed executable, but it has no trusted manifest binding and is not
Vulkan live evidence.

## Interpretation

The diagnostic selected backend name `vulkan`, but it does not independently
prove MoltenVK/provider health, backend font dispatch, or device readback. The
receipt occurs after `fonts.stage_text_configured()` and before batch
consumption, so it proves that an empty staged quad list is observed
pre-dispatch despite a non-empty atlas-pixel array. The precise producer fault remains to
be isolated. The path is not fail-closed, preventing valid cold/warm cache,
Vulkan font execution, device-readback, 300-DPI capture, and event evidence.

The isolated changes used to diagnose the receiver and target routing are not
accepted implementation evidence because the final native probe still faults
and does not reach the post-cold-draw marker. They must not be merged as a
completed fix.

The 2026-07-27 diagnostics also do not prove where the zero-quad state is
introduced. The leading seam remains the transfer from locally produced quads
through `FontRenderBatch.quads` into `_stage_batch`, but a layout or raster
producer failure is still a viable alternative. Empty scalar serialization and
nil-sentinel renderer retrieval make the diagnostic transport itself
untrustworthy. No renderer fix, live PASS, or bootstrap resulted from these
cycles.

The third cycle confirms that adding more scalar fields/getters on the current
owner path is not a trustworthy next diagnostic step: the process still
reaches a native nil-receiver fault before an observable checkpoint. It does
not localize layout, rasterization, quad construction, or staging. In a fresh
session, first localize and fix the aggregate/owner nil-receiver channel using
the existing tracked aggregate-return bug evidence. Only then retry the
focused font producer checkpoint.

### 2026-07-27 direct-slot receiver-lowering checkpoint

A fresh session used three bounded, no-bootstrap native cycles against the
current direct-slot font-owner experiment. Every build compiled 184 modules
with zero compile failures. None is Vulkan live evidence, and none of the
associated source changes is accepted or committed.

- Cycle 1 linked and ran binary SHA-256
  `3a4ac24823af1df930add1614d94db3affb66cea32409e6ab6d4f8da593d87bd`.
  It exited 2 with `engine2d_font_state_native_status=fail-live-face`.
  Disassembly and scalar inspection showed that the owner slot and its
  renderer mutation were present, but `font_owner_count()` projected the raw
  list length `1` across the method boundary while the caller compared it with
  tagged literal `8`. The false comparison short-circuited the TTF check.
- Cycle 2 replaced the count receipt with an internal boolean owner predicate.
  Binary SHA-256
  `da4b24f203e7c626ea1b80db6b60d11914b241cde041520c568da22f4642869e`
  exited 3. `font_owner_ready()` passed and `load_font()` returned true, but
  `font_has_selected_ttf()` returned false. Static inspection showed the
  renderer payload decoded into `x12`; the generated call branched through
  `FontRenderer.has_sffi_ttf` without moving `x12` into receiver register
  `x0`, so `x0` still held the enclosing `Engine2D`.
- Cycle 3 bound the array element to an explicitly typed local before every
  critical `FontRenderer` method call. Binary SHA-256
  `6c0a0c8463428f9ba01ae1f0068db9c87ac8705f078e11b2e5010ae4bf686c29`
  still exited 3 at the same named TTF predicate. Final static addresses show
  the renderer payload in `x12` at `0x1003cc890`/`0x1003cc898` and the
  indirect call at `0x1003cc8a4`, still without an `x0 <- x12` receiver
  reload. The control comparison is `load_font`: it correctly establishes
  `x0` at `0x1003d56f8`/`0x1003d5700` before its call at `0x1003d5710`.

The three-cycle cap is exhausted. This evidence moves the essential next fix
to compiler/backend receiver lowering, with an exact native regression that
must prove array-element-to-typed-local method receivers populate `x0`.
Product-source receiver workarounds and another font probe are not accepted
substitutes. After that compiler source fix passes focused proof, rebuilding
or bootstrapping may be essential to deploy it into the canonical
self-hosted toolchain; no bootstrap was run or authorized by these cycles.
Only then may the Bungee 24 pt / 300 DPI producer check resume.

## Required acceptance gate

1. In a fresh session, localize and fix the aggregate/owner nil-receiver
   channel using the tracked native aggregate-return evidence; do not add
   another scalar checkpoint on the same untrusted owner path.
2. Establish at least one typed scalar checkpoint through the repaired channel
   that cannot serialize a present value as empty or confuse it with the nil
   sentinel. Use it to distinguish layout/raster production from the
   `local quads -> FontRenderBatch.quads -> _stage_batch` transfer seam.
3. A focused native producer probe must use an exact non-empty Bungee string
   at 24 pt / 300 DPI and prove computed font size 100 px, `valid=true`,
   positive quad count, consistent atlas dimensions/pixel count, in-bounds
   nontransparent quad coverage, and matching renderer identity/generation.
4. An empty or inconsistent `FontRenderBatch` must return a named failure
   propagated to the caller, without dereferencing a nil aggregate, with
   evidence that no backend batch method was entered.
5. `Engine2D.draw_text` must retain the selected renderer and record ordered
   Vulkan execution attempts plus target, prove Vulkan success with no CPU
   fallback, and avoid a native receiver fault while retrieving the selected
   renderer.
6. Cold draw must increment rasterizations; warm draw must keep
   rasterizations stable and increment warm hits.
7. Vulkan device readback after text must prove source `device_readback`, a
   positive backend handle, exact framebuffer pixel count, and a text-only
   region-of-interest pre/post delta.
8. Only after those focused native checks pass may the immutable trusted
   harness be rebuilt and the full live capture/event gate retried.

Bootstrap is permitted only if it is essential after the focused producer
passes and a new immutable trusted binary is required.

## 2026-07-27 compiler receiver channel repaired

The exact compiler defect is now fixed and behaviorally proven. MIR already
carried the receiver first, but the direct and indirect Cranelift call
translation loops used bare `arg_vals.push(...)` expressions and discarded
the returned argument vector. Rebinding the returned vector at both sites
preserves the computed receiver for the native call ABI.

The regression uses a distinct target receiver behind `Owner.active[0]`,
binds it to a typed local inside an owner method, and calls a zero-argument
marker method. The target returns `73`; a stale enclosing owner has the same
leading field layout but returns poison marker `11`. The old deployed
compiler faults with exit 132. The patched pure-Simple Stage 3 compiler
(SHA-256
`d030566ddab91c85606d9e209524d402cd30df5b4c1a92971732690cbadfa5d1`)
returns the exact PASS receipt
`native_consecutive_zero_arg_receiver_status=pass`.

This closes acceptance item 1's receiver channel prerequisite but does not
prove the font producer or any Vulkan gate. Stage 4 deployment is separately
blocked by the stale `examples.browser.entity.dom.css_types` import in
`custom_properties.spl`; the shared deployed compiler was left untouched.
Resume at acceptance item 2 using the proven Stage 3 compiler, then continue
through the remaining items in order.

The first post-fix producer run advances beyond the former fault. With the
canonical specialized runtime providers it compiles 184 modules with zero
failures, links, loads the Bungee face, proves the live TTF predicate and exact
identity, then exits 4 with
`engine2d_font_state_native_status=fail-cold-cache`. No receiver fault occurs.
The first draw therefore fails to expose a rasterization increment; whether
the cause is draw/staging production or cache-state write-back remains
unproven. This probe used 24 px and is not the required 100 px receipt.

The session's three producer cycles are exhausted (two link-configuration
failures followed by the runtime result). The next fresh session must inspect
the cold-draw seam without repeating this command, add trustworthy scalar
batch/cache evidence, and only then require exact Bungee 100 px positive
quads/atlas alpha. Vulkan device execution and readback remain unproven.

The Stage 4 full-CLI import blocker is repaired in source by routing custom
properties to the compatible browser-style CSS types in `style.animation`.
The incompatible common render-scene CSS types are not used. A new source
contract pins the required `Initial` variant and `important` declaration
field. Bootstrap/deploy has not been rerun after this repair.

## 2026-07-27 atomic receipt checkpoint after three producer cycles

The earlier receiver-vector fix is necessary but not sufficient for this new
source shape. Two fresh producer binaries fault identically before the cold
draw. Apple crash reports place the top frames at
`FontRenderer.receipt_cache_rasterizations_zero`,
`Engine2D.font_receipt_reset_cache_stats`, and `spl_main`.

Cycle-3 disassembly is decisive: the typed renderer is held in `x24`; native
code moves `x24` to `x0` before `reset_cache_stats`, then calls
`receipt_cache_rasterizations_zero` without a new `mov x0, x24`. Because the
unit-returning call may leave nil in `x0`, the receipt faults. This is not the
older lost-argument-vector bug and remains an open compiler regression.

The bounded source checkpoint now:

- resets and verifies cache counters inside one mutating
  `FontRenderer.reset_cache_stats_receipt()` call;
- constructs the 24-point/300-DPI `FontRenderConfig` directly in Engine2D;
- stores only a boolean `size == 100` receipt across the class boundary;
- admits a caller-owned plan using independent nonempty gates, without exact
  cross-boundary numeric equality; and
- binds every renderer receipt to an explicitly typed local before calling it.

No fourth native producer run or bootstrap is permitted in this session.
Therefore exact Bungee 100-pixel quads, ROI alpha, cold/warm cache behavior,
Vulkan execution, and device readback all remain unproven.

## 2026-07-27 bounded producer cycles 4–6

Three fresh no-bootstrap producer builds each compiled 184 modules with zero
failures using the admitted pure-Simple Stage3 compiler and the canonical
Winit/WM/C runtime providers.

Cycle 4 proved the atomic reset receipt reaches configured staging. It then
faulted in `Engine2D.font_receipt_size_100px`; the crash report records
`x0=0` at the immutable zero-argument method. Converting the diagnostic
receipts to the proven mutable-receiver ABI removes that fault.

Cycle 5 exits normally at the exact receipt
`engine2d_font_state_native_status=fail-positive-quads`. Typed renderer
staging/write-back is now explicit. Cycle 6 repeats that exact result after
rebinding every returned array used by fallback layout, atlas metadata,
quad/dirty construction, and `GlyphCache.insert`. The Cycle-6 binary SHA-256
is `746a2a08148b9b12ca41aa62ca932341418ac00c92cdebd40ff31fea89ccd283`.

The strongest current evidence is therefore:

- exact Bungee load and identity: PASS;
- function-local 24 pt at 300 DPI equals the 100-pixel receipt: PASS;
- cold reset, draw admission, plan admission, and staged-valid state: PASS;
- staged quads: FAIL (zero);
- atlas ROI alpha, cold rasterization count, warm cache hit, Vulkan execution,
  and device readback: not reached.

The three-cycle cap is exhausted. Preserve Cycle 6 and inspect the glyph
aggregate/raster material in a fresh session; do not convert the allocated but
empty 1024² atlas into positive evidence.

The next bounded diagnostic should use three boolean-only phase receipts:
local `quads` nonempty immediately before constructing `FontRenderBatch`,
inbound `batch.quads` nonempty on entry to `_stage_batch`, and stored
`self.staged_quads` nonempty after assignment. This distinguishes local append,
array-bearing aggregate transport, and staged-field assignment without relying
on untrusted numeric or aggregate returns. The allocated atlas length alone
does **not** prove glyph insertion or alpha coverage.

## 2026-07-27 bounded producer cycles 7–9

Cycle 7 establishes `local quads = false`; therefore the array-bearing
`FontRenderBatch` boundary is not the active first failure. Cycle 8 refines
this to `layout = true` and `positive glyph dimensions = false`. Atlas index,
quad append, inbound batch, stored quads, ROI alpha, and cache evidence are not
reached.

All three cycles compiled 184 modules with zero failures. The canonical font
modules now rebind value-returning pushes for rasterizer pixels, WFFI argument
arrays, SFFI layout/pixel arrays, cache entries, fallback/quads/atlas metadata,
shaped identities, and advance-layout arrays. Cycle 9 nevertheless repeats
the exact `engine2d_font_state_native_status=fail-text-glyph` receipt. Cycles
8 and 9 also have an identical binary SHA-256,
`7db8cc35eeab4fd6e406711c043cfa64f16a437ae3ecf858e0d1926990c284dc`,
showing those source corrections did not alter this compiled closure.

The next fresh-session diagnostic belongs inside `FontRenderer.get_glyph`.
Use boolean-only fields reset for each configured stage and set at these
causal boundaries: selected rasterizer maps the codepoint; `rasterize` returns
non-nil; raw glyph width/height are positive; raw pixel length matches their
product; same-module reconstructed `CachedGlyph` is positive; caller receives
positive dimensions. This will distinguish SFFI call/bitmap transport,
cross-module adapter construction, and `CachedGlyph` return transport without
printing or returning the suspect aggregate.

## 2026-07-27 bounded producer cycles 10–12

Cycle 10 localizes the first invalid material to the selected-outline bitmap
boundary. Exact receipts pass for face mapping, non-nil bitmap, and positive
bitmap dimensions, then fail at
`engine2d_font_state_native_status=fail-glyph-bitmap-pixels`. The adapter,
cache, and second `get_glyph` call are downstream and are not the current first
failure.

A read-only path audit establishes that no `libspl_fonts.so` candidate is
active on this macOS lane. The path is
`load_selected -> _rasterize_selected_outline ->
sfnt_rasterize_codepoint_parts -> GlyphBitmap?`. Cycle 11 rebinding of all
remaining `sfnt_glyf` array pushes changed the binary but retained the exact
pixel mismatch.

Cycle 12 experimentally wrapped the tuple with mutable outputs and a boolean
result, but it regressed to `fail-glyph-bitmap-return`. High review identified
two tuple-return hops still underneath the wrapper
(`_sfnt_rasterize_glyph_parts -> sfnt_rasterize_codepoint_parts -> wrapper`).
The regressing call-site experiment was reverted before commit. All three
cycles compiled 184 modules with zero failures using the retained pure-Simple
Stage3 diagnostic compiler; no bootstrap was run.

The next session must instrument, once, the source bitmap pixel consistency and
the tuple handoff inside the common `sfnt_glyf` module. The fix must eliminate
the aggregate-return chain end-to-end, using a live-receiver result owner
(scalar metrics plus owned pixel field) if source pixels are valid. A source
FAIL selects the inner rasterizer or its `SfntGlyfBitmap` Option return.
Vulkan live evidence remains blocked.

## 2026-07-27 bounded producer cycles 13–15

The attempted end-to-end live-owner path removes the four known pixel-bearing
return hops from selected-font production. Cycle 13 nevertheless exits at the
new first receipt, `fail-glyph-source-local-pixels`. Cycle 14 replaces the
coverage loop's rebound pushes with exact-size allocation and indexed writes;
the result is identical. Both builds compile 184 modules with zero failures.

Cycle 15 returns a scalar phase code from the SFNT receiver and transports it
through typed `FontRasterizer`, `FontRenderer`, and `Engine2D` receipts. The
probe prints `fail-glyph-source-status-` with no scalar interpolation and exits
43. This means the receiver/status transport is not authoritative on this
compiler; it does not prove the raster loop itself failed. No bootstrap was
run, and the three-cycle cap is exhausted.

The next design must keep ownership in one module and cross boundaries only
through a raw scalar handle/address plus scalar accessors. A module-local raw
descriptor can hold width, height, advance, bearings, byte count, and owned
coverage. The SFFI owner should copy the bytes once, release the descriptor,
and construct `CachedGlyph` locally. Do not wrap the descriptor in Option,
tuple, or an aggregate receiver.

## 2026-07-27 bounded producer cycles 16–18

Cycle 16 provides authoritative AOT evidence that an imported omitted-return
free function can mutate fixed indexed elements in caller-owned `[i64]` and
`[u8]` arrays across the common-to-SFFI boundary. Exact metadata and byte
sentinels survive; execution then reaches the pre-existing
`fail-glyph-bitmap-pixels`.

Cycles 17–18 apply that shape to selected-glyph measurement and rendering.
Both compile 184 modules with zero failures. Cycle 17 fails before publishing
a bitmap; Cycle 18's boolean-only gates localize this to
`fail-glyph-void-measure`. The render call is never reached, so this does not
invalidate caller-owned pixel-plane mutation.

The next bounded diagnostic belongs inside
`sfnt_glyf_measure_codepoint_into`. It must stamp fixed metadata slots
monotonically after input validation, `parse_offset_table`, cmap mapping, table
validation, outline parsing, horizontal metrics, and bounds/dimensions, with
the completion cookie written last. No bootstrap was run.

## 2026-07-27 bounded producer cycles 19–21

Cycle 19 proves the authoritative owner-local Bungee blob and the blob
extracted into `FontRenderer` have identical fixed fingerprints: exact
118996-byte length, SFNT header, sampled bytes, weighted sample, and completion
cookie. It then reproduces `fail-glyph-bitmap-pixels`.

Cycle 20 passes monotonic stamps through parse, cmap, table validation, metric
bounds, outline parsing, and horizontal metrics. Cycle 21 further passes
drawable-command, bounds, and dimension stamps, then returns to the exact
bitmap-pixel mismatch. Each cycle compiles 185 modules with zero failures.

Therefore the selected blob, outline parser, metrics, and geometry are sound at
the diagnostic boundary. The active first loss remains after raster coverage
is produced and before/while pixel-bearing `SfntGlyfBitmap`, tuple, and
`GlyphBitmap?` results are published. The next fix should preserve the
owner-local parsing path and publish coverage through a raw scalar descriptor
or owner-local void copy, without duplicating parse work in `get_glyph`.
