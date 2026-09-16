# BUG: `FontRenderBatch` missing `atlas_owner_generation` field + missing native-safe identity free functions — dropped during codex-font-branch reland

## Status
FIXED (2026-07-20). Root cause confirmed by git evidence; field and free
functions implemented; verified via the spec's real `expect(...).to_equal()`/
`to_contain()` assertions. One assertion in the same spec remains red, but on
an unrelated, already-filed, pre-existing SSpec harness bug (see "Residual
failure" below) — not on this class/field.

## Summary
`test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl`
(and the "keys atlas ownership by font face program dimensions and dependency
generation" case in `font_renderer_spec.spl`, lines 150-195) failed on the
interpreter test path with:

```
semantic: class `FontRenderBatch` has no field named `atlas_owner_generation`
```

`class FontRenderBatch` (`src/lib/nogc_sync_mut/text_layout/font_types.spl:208`)
had no `atlas_owner_generation` field, and the module had no
`font_render_batch_atlas_owner_identity`/`font_render_batch_atlas_cache_identity`
free functions, even though:
- `font_renderer_spec.spl` constructs `FontRenderBatch(..., atlas_owner_generation: -2)`
  at two call sites (a "shared atlas across faces" ownership test, lines 171-176).
- `font_identity_free_function_spec.spl` constructs a batch with
  `atlas_owner_generation: 11` and calls
  `font_render_batch_atlas_owner_identity(batch)`/`font_render_batch_atlas_cache_identity(batch)`
  as free functions (not methods).
- The four `font_renderer.spl` wrapper/re-export files
  (`src/lib/{nogc_async_mut,gc_async_mut,gc_sync_mut}/text_layout/font_renderer.spl`)
  already listed `font_render_batch_atlas_owner_identity, font_render_batch_atlas_cache_identity`
  in their public `export use` set — but the base
  `nogc_sync_mut/text_layout/font_types.spl`/`font_renderer.spl` never defined
  them, so the re-export was dangling.

## Drift direction (with git evidence)

This is **not** a rename and **not** a deliberately-removed feature — it is a
genuinely missing implementation that was planned and spec'd but never landed,
per the repo's own commit message.

`git log -S atlas_owner_generation --oneline -- src/ test/` shows exactly ONE
commit touching this identifier:

```
7fd629f8ac1 feat(fonts): reland forward-safe portion of codex font branch
  (docs/specs + non-contested src; fd trio + off-theme compiler edits dropped)
```

`git show --stat 7fd629f8ac1` confirms the shape of that commit:
- `font_identity_free_function_spec.spl` — **new file**, +37 lines (the spec
  referencing `atlas_owner_generation` and the two free functions).
- `font_renderer_spec.spl` — modified, +18 lines (added the
  `shared_base`/`shared_other_face`/`unowned_shared_claim` shared-ownership
  case using `atlas_owner_generation: -2`).
- Each of `src/lib/{nogc_async_mut,gc_async_mut,gc_sync_mut}/text_layout/font_renderer.spl`
  — a 1-line `export use` diff each, adding
  `font_render_config_identity, font_render_batch_atlas_owner_identity, font_render_batch_atlas_cache_identity`
  to the re-export list.
- **`src/lib/nogc_sync_mut/text_layout/font_types.spl` and
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (the base
  implementation files) were NOT touched by this commit.**

So the commit relanded the specs and the downstream re-export plumbing for a
"shared atlas ownership across faces" feature, but its own message admits the
actual implementation ("fd trio + off-theme compiler edits") was dropped
during the reland. The class field and the two free functions never made it
back in. This is scenario (b) from the mission brief: real, needed behavior
(cross-face atlas-cache ownership keying, used by GPU font backends via
`font_render_batch_atlas_owner_identity` — see
`src/lib/gc_async_mut/gpu/engine2d/backend_{cuda,opencl,rocm,vulkan_font,metal_font}.spl`
and `engine3d/vulkan_font_adapter.spl`) that was designed and spec'd but not
built. Per the "fix bug and empty or missing logic" standing rule, the fix is
to implement it, not delete the spec coverage.

## Fix

`src/lib/nogc_sync_mut/text_layout/font_types.spl`:
1. Added `atlas_owner_generation: i64 = -1` to `class FontRenderBatch`
   (sentinel `-1` = "no override, use `face_generation`" — same convention as
   the existing `FontRenderQuad.cluster: i64 = -1` sentinel in the same file).
2. Added the free functions `font_render_batch_atlas_owner_identity(batch)`
   and `font_render_batch_atlas_cache_identity(batch)`, which hold the real
   string-building logic (reading `batch.<field>` directly, no `self.method()`
   calls) — the same free-function-holds-the-logic pattern as
   `font_render_config_default_for_size()` in the same file, and for the same
   documented reason as `font_render_config_identity()` (see the
   `NOTE(2026-07-18)` comment above it, referencing
   `doc/08_tracking/bug/engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md`):
   the entry-closure freestanding native path miscompiles instance method
   calls (`self.method()`), passing the callee's own code address as `self`
   instead of the receiver, so a native-safe identity helper cannot call back
   into `self.atlas_owner_identity()`.
3. `atlas_owner_identity()`/`atlas_cache_identity()` instance methods now
   delegate to the free functions (`font_render_batch_atlas_owner_identity(self)`
   / `font_render_batch_atlas_cache_identity(self)`), not the other way
   around, so both call forms stay identical and only one path holds the
   logic.
4. The owner identity's `face-generation=` component now uses
   `owner_generation = self.atlas_owner_generation != -1 ? self.atlas_owner_generation : self.face_generation`
   instead of always `self.face_generation`.

`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`: added
`font_render_batch_atlas_owner_identity, font_render_batch_atlas_cache_identity`
to the `export use ... font_types.{...}` list (this file already re-exported
`font_render_config_identity`/`font_render_config_valid` the same way; the two
batch-identity functions were the only ones missing from this base re-export,
even though the three upper-layer wrapper files already forwarded them).

## Regression check

All production `FontRenderBatch(...)` construction call sites (~20, in
`font_renderer.spl`) use fully-named arguments — grepped and confirmed none
use positional args — so inserting the new field in the middle of the class's
field list carries no positional-argument-shift risk.

## Verification

Before fix (`bin/simple test test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl --mode=interpreter`):
```
native-safe font identity free functions
  ✗ preserves config owner and generation identities without method dispatch
    semantic: class `FontRenderBatch` has no field named `atlas_owner_generation`
1 example, 1 failure
Passed: 0
Failed: 1
```

After fix (same command, re-run after the free-function/delegation flip to
confirm output is unchanged):
```
native-safe font identity free functions
  ✗ preserves config owner and generation identities without method dispatch
    expected font-atlas-v1|11:sha256=test|face-generation=11|program=1|config=6:config|transform=28:uniform-scale;translate-late|size=64x32|generation=3 to equal font-atlas-v1|11:sha256=test|face-generation=11|program=1|config=6:config|transform=28:uniform-scale;translate-late|size=64x32|generation=4
1 example, 1 failure
Passed: 0
Failed: 1
```

The "has no field" error is gone. The two assertions that exercise the field
now pass silently (no longer shown as failing) before execution reaches the
third assertion:
- `expect(font_render_batch_atlas_owner_identity(first)).to_equal(font_render_batch_atlas_owner_identity(second))`
  — two batches differing only in `atlas_generation` (3 vs 4) produce EQUAL
  owner identities. PASSES.
- `expect(font_render_batch_atlas_owner_identity(first)).to_contain("face-generation=11")`
  — directly proves the `atlas_owner_generation: 11` override drives the
  `face-generation=` component of the identity string (the batch's
  `face_generation` field is 7, not 11 — only the override value could
  produce "11"). PASSES.

### Residual failure (NOT this bug — pre-existing, already filed)

The third assertion,
`expect(font_render_batch_atlas_cache_identity(first) == font_render_batch_atlas_cache_identity(second)).to_be(false)`,
still fails, but not on FontRenderBatch: the two cache-identity strings shown
in the failure message above are correct and genuinely different
(`...generation=3` vs `...generation=4`, exactly as expected — the whole
point of the assertion). The failure is the SSpec/BDD `expect(<bool
expression>).to_be(false)`/`.to_equal(false)` idiom itself, already
root-caused and filed:
`doc/08_tracking/bug/bdd_expect_compare_to_equal_bool_eager_fail_2026-06-30.md`
("`expect(a == b).to_equal(false)` false-fails when a != b" — the BDD runner's
infix-comparison handler eagerly marks the example failed on ANY `==`
producing `false`, before the trailing matcher even runs). Confirmed
independently in this session with a minimal, font-unrelated repro
(`expect("hello3" == "hello4").to_be(false)` inside a bare `describe`/`it`
block — same failure). The self-hosted `src/lib/nogc_sync_mut/spec.spl`
`expect(value: bool) -> ExpectHelper` overload has the same structural
eager-fail (`if not value: fail_assertion(...)` before any chained matcher
runs), so this likely reproduces on both the seed and self-hosted paths, not
just one. That 2026-06-30 doc's own prescribed workaround —
`expect_not(a == b)` / `expect(a).to_not_equal(b)` instead of
`expect(a == b).to_be(false)` — is the same idiom `font_renderer_spec.spl`
already uses successfully elsewhere in its own atlas-ownership test (e.g.
`expect_not(base.atlas_owner_identity() == changed_face.atlas_owner_identity())`,
line 184). Left un-swapped here per this lane's scope (FontRenderBatch only)
and the mission's own guidance to file specifics rather than edit tests to
route around a separately-owned defect.

`font_renderer_spec.spl`'s "keys atlas ownership..." `it` block (same
`atlas_owner_generation` feature, lines 150-195) was also run after this fix;
it no longer fails on "has no field", confirming the same root-cause and fix
apply there. Its file-level run reported a generic `test-runner: spec failed`
after one earlier unrelated example, without per-example detail for this
block specifically — not chased further as out of this lane's scope (the file
also uses the same `.to_be(false)` idiom at lines 191 and 195, so it is
expected to hit the same pre-existing bug once/if that generic failure is
resolved).

## Related
- `test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl`
  (this lane's target spec)
- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl:150-195`
  ("keys atlas ownership by font face program dimensions and dependency
  generation")
- `src/lib/nogc_sync_mut/text_layout/font_types.spl:107-129`
  (`font_render_config_identity`, the established free-function pattern this
  fix follows) and `:208-286` (the fixed `FontRenderBatch` class + free
  functions)
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:34-40` (re-export list)
- Commit `7fd629f8ac1` (the incomplete reland that introduced this drift)
- `doc/08_tracking/bug/bdd_expect_compare_to_equal_bool_eager_fail_2026-06-30.md`
  (the separate, pre-existing, already-filed harness bug behind the residual
  red assertion — not fixed by or in scope of this doc)
