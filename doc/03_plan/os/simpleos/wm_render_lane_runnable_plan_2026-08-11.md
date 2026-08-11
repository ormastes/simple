# WM + render lane SimpleOS-runnable — completion plan (2026-08-11)

**Goal:** rung (d) — SimpleOS boots under real firmware and the WM actually
renders, proven by a NON-UNIFORM PPM screendump (pixel-variance check), never by
file existence.

## Dependency chain (this is the plan's spine)

```
runtime_native.c compiles  [DONE — a1f3adeff791]
  -> bin/simple native-build works (seed lane)     [DONE — ./build/native/hello runs]
  -> And/Or codegen validation, sha256_core fix, in-guest full CLI

bootstrap/stage3/simple native-build SIGSEGV        [SEPARATE — NOT gated by the above]
  -> root cause: MIR field-index collision in stage3's own borrow-checker,
     upstream of any runtime_native.o link
  -> stage3-dependent items (unstripped stage3, in-guest full CLI's
     seed-cranelift enum path) stay blocked until THIS is fixed
```

**Correction (2026-08-11):** this plan originally claimed the stage3 SIGSEGV was
downstream of `runtime_native.c` not compiling. Diagnosis proved that wrong —
the crash is entirely internal to stage3's HIR/MIR lowering, before any link
step. Track A step 3 (native-build works) and Track A step 4 (stage3 SIGSEGV)
are independent; do not sequence one behind the other.

## Track A — restore a compile path

1. **`src/runtime/runtime_native.c`** — DONE. The unsigned-box fix landed and is
   verified by the new compile guard: `runtime_native.c` now compiles clean.
2. **C-runtime compile guard** (`check-c-runtime-compiles-push.shs`) — landed
   `04848434af0c`, kept **advisory**, not mandatory. It is honestly RED on one
   remaining never-compiled file: **`src/runtime/platform/async_linux_uring.c:733`
   — `use of undeclared identifier 'NULL'`, missing `<stddef.h>`**. Same class as
   the original defect, previously unfiled, still unowned. Fix it, then flip the
   guard to mandatory and wire into `pre-push-conflict-tree-guard.shs` — that is
   the written promotion criterion.
3. **`bin/simple native-build` now works** — `a1f3adeff791` implemented the
   missing unsigned-value box in `runtime_native.c`, derived byte-for-byte from
   the pure-Simple twin `simple_core/core_values.spl` (not guessed — a guessed
   magic value would have compiled and passed every guard while silently
   disagreeing with the twin). `./build/native/hello` runs. Exit 1 → 0.
4. **`bootstrap/stage3/simple native-build` still exits 139 (SIGSEGV) — CORRECTED,
   this plan's dependency chain was wrong.** Diagnosis (2026-08-11, re-running the
   documented repro against the deployed stage3 binary) found **no causal path
   from `runtime_native.c` to this crash at all**: it's a cross-module MIR
   field-index collision in `MirLowering.resolve_field_index`
   (`src/compiler/50.mir/_MirLowering/function_lowering.spl`) — the borrow
   checker reads `NLLChecker.errors` at the wrong struct offset because a
   module-local SymbolId collides across an entry-closure build. This happens
   entirely inside stage3's own HIR/MIR-lowering and borrow-check passes,
   **before** stage3 ever links against `runtime_native.o`. A partial fix landed
   2026-08-07 (module-qualified `struct_field_order` tier) but the currently
   deployed stage3 binary — built after both that fix and the `runtime_native.c`
   fix — still crashes: either the fix is present-but-unexercised, or a second
   collision instance exists downstream. See
   `doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`
   for the full investigation. This item does **not** depend on Track A step 3.
5. **And/Or codegen fix — LANDED (`f35ef97dc58c`)**, sabotage-verified (revert
   the two `lower_cond_expr` call sites → spec goes RED, restore → GREEN). Caveat:
   this is a source-content regression guard, not a runtime execution spec — no
   self-hosted binary was available this session to exercise native/JIT codegen
   directly, so the fix's effect at runtime is still unproven by execution.
6. **sha256_core value-boxing — STILL OPEN, and harder than first framed.**
   Further investigation found the corruption is not consistently ×8 (sometimes
   ÷8, depending on call shape) — the original "shift-left-3" framing was too
   narrow. Traced to somewhere among ~10 nested calls inside
   `sha256_process_block`, spanning a third module
   (`std.common.crypto.types`), not isolated to one call boundary. FIPS vectors
   (empty string, "abc") still fail on the live seed JIT lane. No fix landed —
   correctly, no regression specs were added either (specs-last discipline
   held). `sha256_simd_parity_spec.spl` does assert real FIPS vectors (not
   vacuous) but why it isn't catching this live corruption is still unexplained
   — both `bin/simple <file>` and `bin/simple test <file>` timed out at 60s
   when checked. **Next step for a future session:** bisect the ~10 nested
   calls individually rather than assume the boxing family from other modules
   applies unchanged here.

**Guard duplication found and resolved (2026-08-11):** two agents independently
built overlapping C-runtime-compiles pre-push guards
(`check-c-runtime-compiles-push.shs` @ `04848434af0c`, and
`check-c-runtime-compiles.shs` @ `a1f3adeff791`) without knowing about each
other. `check-c-runtime-compiles-push.shs` survives as canonical — it was
already the mandatory, wired-in guard (vcs.md, `pre-push-conflict-tree-guard.shs`)
and had materially stronger coverage: recursive scan of `src/runtime/**/*.c`
(the sibling script globbed only the top-level dir, missing every file under
`src/runtime/platform/**` including `async_linux_uring.c`, the exact file this
same guard's own promotion history found broken) and an 8-fixture selftest vs
5. The sibling's one real strength — compile flags matching the actual build
lane (`-std=gnu11`, `-I src/runtime/platform`) — was merged into the canonical
script; the sibling file was deleted.

## Track B — rung (d) (independent of A)

**New blocker found and partially fixed:** an untracked in-flight file
(`src/os/sosix/fs/ipc_codec_v1.spl`, another session's work) that's pulled into
the 1537-file kernel closure triggered a real parser defect — a statement-
leading `out.method(...)` call gets hijacked because the parser's contract-
block dispatcher decides on a bare `out`/`out_err` token instead of checking
for the disambiguating `(`. Same family as the already-fixed
`identifier_named_grid` hijack bug. **Fixed in the Rust seed
(`0ebc775977`)**, family-swept (`in`/`invariant`/`requires`/`ensures`/
`decreases` don't share the shape; `fn f(out x: T)` modifier-position is a
separate, still-open sub-bug). **Checked against the self-hosted frontend —
no fix needed there**, but for a more fundamental reason than "already
correct": `src/compiler/10.frontend` has **no `out`/`out_err` contract-block
grammar at all** (`keyword_lookup` has no such branch, falls through to plain
`TOK_IDENT`), so the hijack literally cannot occur — there's no keyword
dispatch to trip. This means design-by-contract `out(ret): ...` syntax is
currently **seed-only**, a feature gap, not parity with the seed.
**Blocking everything regardless: no self-hosted binary exists on this
machine right now.** Every binary checked (`bin/simple`,
`bin/release/.../simple`, `build/bootstrap/stage3/.../simple`) prints the
Rust-seed warning banner; `build/bootstrap/stage2/` is still empty from the
earlier concurrent `bootstrap-from-scratch.sh` wipe. **A fresh self-hosted
build is now the actual next blocker for any real gate run**, ahead of
whatever `ipc_codec_v1.spl` does next.

**Correction, twice over — the real picture is worse than either investigation
found alone.** A full-bootstrap attempt tonight failed at phase4:monomorphize
with `error: ... src/compiler/backend/backend/interpreter.spl: unresolved type:
Symbol`. Static-source investigation found the fix already exists at HEAD
(TAL2/TAL3, 2026-08-01/08-04) and hypothesized the failed run used a stale
stage3. **But checking the actual machine state directly (not another
investigation) found: `systemctl --user list-units --all | grep
simple-stage4` lists 25 bootstrap attempts tonight, ALL failed, none
currently running.** The most recent (07:18-07:56 UTC) never even reached the
Symbol bug — **Stage 3 self-host was `Terminated` (exit 143, killed) before
Stage 4 could run at all**: `warning: stage3 self-host failed (exit 143);
Stage 4 unavailable` / `error: full CLI build requires a verified pure-Simple
stage2/stage3 compiler; refusing seed fallback`. Under tonight's contention
(many concurrent sessions, 32 CPUs saturated), **resource exhaustion is
killing Stage 3 before code correctness is even reachable as a question.**
The Symbol-bug hypothesis is neither confirmed nor falsified — it's simply
never been tested against a Stage 3 that survives long enough to reach it.
**Not relaunching another bootstrap attempt into the same contention** — next
session should retry once the machine is genuinely quieter, and specifically
watch whether Stage 3 completes at all before worrying about Stage 4.

Current blocker order, each replacing the last as it clears:

1. **Guest heap exhaustion — FIXED (`2175a16514bb`), UNVERIFIED.** Root cause:
   `rt_extras.c:4102 rt_byte_array_new` discarded its `capacity` argument,
   forcing doubling-growth allocation (1,2,4,8,16,32 MiB) on every large asset
   read; `free()` is a no-op on the guest's bump heap, so every intermediate
   buffer leaked permanently. A 24 MiB asset allocated ~63 MiB. Neither prior
   suspect (font-config fix, 1514→1515 closure growth) was the cause — both
   ruled out directly, they only shifted the working set across a pre-existing
   leak's edge. **Verification blocked**, not failed: a concurrent
   `bootstrap-from-scratch.sh --full-bootstrap` emptied `build/bootstrap/stage2/`
   and exited without redepositing a binary, so the gate run immediately failed
   `simple-bin-forbidden` (only the Rust seed remained) — not a real product
   signal. Needs a gate re-run once a pure-Simple compiler binary exists again.
2. `[hda-init] unavailable status=-5`.
3. VFS `blockdevice-dispatch-codegen-bug`.
4. Capture + PPM variance assertion.

**Attribution still open:** the run that reached `wm=live` hashed 1514 files; the
panicking run hashed 1515 *and* carried the engine2d font-config fix
(`e86b7eca9d72`). The fix is landed but unvalidated.

**Gate mechanics that must not be re-learned:** set BOTH
`SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS` and `..._WORKER_TIMEOUT_SECONDS`,
worker **strictly less** than outer. The name without `_SECONDS` is a silent
no-op. Only `kernel_input_verdict=PASS — <n> file(s) hashed` makes a run
trustworthy; contention reasons are not product results. A freshly-timestamped
run dir holding old content is the NORMAL signature of a run that has *started*.

## Track C — blink render lane

- Stage 1: colour parity **landed** (`b99387ee1ace`, sabotage-verified: restoring
  the opaque-black default turns exactly 3 specs RED). At-rules (`@media`/
  `@supports`/`@layer`) + 28 shorthand properties **landed** (`47246c1cd5b9`) —
  `bool?` with `nil`=not-evaluated preserved throughout, unevaluable blocks
  tracked in `unevaluated` rather than dropped silently. Float line-boxes + rule
  index still in flight.
- Stage 5 render adapter **landed** (`f17811ab90a1`) — `BROWSER_RENDER_LANE_DEFAULT
  = LIVE`, override via `SIMPLE_BROWSER_RENDER_LANE`, both lanes compiled and
  reachable, rollback is one line.
- **Colour parity is CLOSED** — superseded the "~9 vs ~140 named colours"
  estimate above; a sibling lane repointed `cascade.spl` at
  `common.color.css.parse_css_color` and it's pixel-verified through the
  adapter (`red`, `rgb()`, `hsl()`, `#hex`, `tomato` all match).
- **Real remaining exit criteria** (written into `render_lane.spl` beside the
  flag): (1) colour — CLOSED; (2) text glyph paint — **CLOSED (`d3da55c283d`)**,
  real glyphs via shared `common.ui.glyph_bitmap_8x16` 8x16 VGA font, sabotage
  oracle proves it's not a no-op/solid-fill (4/4, bounds one glyph's painted
  pixels strictly 10-128), stated honest limits (fixed 8x16 scale, no AA, no
  line wrap, ASCII 0x20-0x7E only, `<style>`/`<script>` text excluded); (3)
  inline `style=` — **CLOSED for real this time (verified at `3d80fd897723`).**
  Renamed to `blink_parse_declarations`/`CssDeclaration` (blink-scoped), no
  collision with the unrelated `gc_async_mut/gpu/browser_engine/style_block.spl`
  module's `parse_declarations`/`CssDecl`. (An earlier report of this as CLOSED
  was premature — described completed local work without confirming a landed
  sha, and the first landing attempt would have collided; corrected, then
  actually fixed and landed.)
  (4) borders/shadow — **CLOSED (`3b0465891bd9`)**, up to 4 border edge rects
  + 1 offset box-shadow rect per box, sabotage-verified (6/6, exact rect
  counts not a flat-fill shortcut); transforms/gradients explicitly deferred,
  not attempted. (Note: the text-glyph-regression concern raised earlier
  turned out to be muddled shared-worktree state, not a real bug — re-verified
  4/4 pass against actual origin content.)
  (5) stylesheet sources — **UA default stylesheet CLOSED (`8836deae37b4`)**,
  ~30 tags' display defaults, `a{color:blue}`, merged at UA specificity below
  author rules; `<link>` explicitly deferred — the adapter takes an in-memory
  HTML string with no fetch capability, closing this needs either real fetch
  or a signature change, left to whoever owns the interface. (6)
  `check-electron-simple-web-layout-bitmap-evidence.shs` — **run, and found
  the gate itself can't test this criterion.** Its fixture imports
  `simple_web_render_html_to_pixels` from `browser_engine` directly, never
  `render_lane.browser_render_html_to_pixel_array`, and never reads
  `SIMPLE_BROWSER_RENDER_LANE` — live-lane and blink-lane runs produced
  byte-identical output because the flag is never consulted. Separately, both
  runs also hit `simple-layout-render-failed` (SIGSEGV, exit 139) rendering
  the gate's scene through the live renderer before blink is even reached —
  consistent with tonight's no-working-self-hosted-binary situation, not a
  blink defect. Filed:
  `doc/08_tracking/bug/electron_simple_web_layout_gate_bypasses_render_lane_flag_2026-08-11.md`.
  Criterion 6 needs the gate fixed before it can be evaluated at all. Inline
  `style=` (3) is genuinely CLOSED (verified collision-free at `3d80fd897723`)
  — the flip now stays blocked on (6) only.
- Note: blink has **zero production callers** in `src/app/**` or `src/os/**`.
  This is a build-out, not a repair.

## Track D — uncovered

FPGA/board bitstream (deferred 3×). Board-runnable rule still applies: a
QEMU-only result is a defect, not a completion.

## Process findings that change how work lands here

- **Guards-then-push is livelocked.** Origin advances every ~60s; the divergence
  guard takes ~50 min. Land the guard-verified byte-identical delta via a tight
  fetch/rebuild/push loop, then re-guard the landed range — and state the
  ordering deviation explicitly every time.
- **`git status` lies.** Local HEAD is hours behind origin, so origin-identical
  files read as `??`/`M`. Compare blobs against a freshly fetched tip with
  `git rev-parse --verify` (without `--verify` it echoes the input and fakes
  drift). This misled three separate decisions.
- **`rules.sdl` was never actually broken tonight — a stale phantom staged
  deletion faked it.** ~10 agents independently hit `check-rules-sdl.shs`
  ERRORing and used `--no-verify` to route around it, believing `rules.sdl`
  was uncommitted. It was already landed at origin (`86d39fbe8d2`,
  `a369b5578bc`), byte-identical locally and remotely. The real defect: this
  shared worktree's git index carried a stale `git rm --cached`-style staged
  deletion of `rules.sdl` from an earlier session, so `git status` showed it as
  both `D` and `??` simultaneously while the file sat safely committed. Fixed
  with `git restore --staged rules.sdl`. Lesson: a gate failure that "everyone
  hits" is worth checking against committed refs before assuming the content is
  really missing and reaching for `--no-verify` — `git status` in this worktree
  is not reliable evidence of what's actually committed.
- **Five measurement errors this session, one shape:** a query answered
  correctly, interpreted against an assumption that does not hold here (`pub` is
  not the export form; a loose `pgrep` counts probe shells; a glob that doesn't
  descend). Every one was caught by *executing* something, not by inspecting
  declarations. Prefer execution oracles.
