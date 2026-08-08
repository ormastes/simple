# Cross-Workstream Review — WS-A..WS-E detail plans

2026-08-06. Read-only review of the five detail plans + design doc + umbrella plan +
`.spipe/simpleos-screens-render-lane/state.md`. Every contested fact re-verified against source.

---

## 1. File-ownership collisions

### 1.1 Consolidated ownership matrix (⚠ = contested)

| File | A | B | C | D | E | Verdict |
|---|---|---|---|---|---|---|
| `os/kernel/boot/rc_conf.spl`, `init_services.spl`, `os/installer/image_builder.spl` | A1/A3 | | | | | A |
| `os/compositor/backend_factory.spl` | A2/A4 | | ⚠C5 "wiring" | | | **A owns; C5 requests only** |
| `scripts/check/check_simpleos_multiconfig_live_evidence.spl` | ⚠A5 | | | | ⚠E4.2 | **collision → 1.2** |
| `os/simpleos_config_matrix.spl:594` | ⚠A5 | | | | ⚠E4.1 | **collision → 1.2** |
| `common/ui/screen_host.spl`, `host_input_event.spl`, `backend.spl` | | B1 | consumes | | | B |
| `common/ui/wm_app_process_contract.spl` | | B1 (struct) | ⚠C5 lists | | | **B1 owns; C read-only** |
| `common/ui/showcase_catalog.spl` | | B8 | | | | B |
| `app/ui_showcase/**`, `examples/06_io/ui/widget_showcase_gui.spl` | | B2–B7 | | | | B |
| `os/drivers/input/{input_event,host_input_adapt,ps2_keyboard,ps2_mouse}.spl` | | | C1–C3 | | | C |
| `os/compositor/{input_backend,compositor,hosted_input_sdl2}.spl` | | | C1/C2/C4 | | | C |
| `os/hosted/hosted_entry.spl`, `app/ui.browser/app.spl` | | | C3 | | | C |
| `os/compositor/{fb_backend,browser_backend}.spl` | implied | disclaimed | disclaimed | | | **UNOWNED → 1.3** |
| `os/compositor/screen_app_2d.spl` | not planned | | ⚠C5 assumes A2 | | | **UNOWNED → 6.1** |
| `nogc_sync_mut/gpu/engine2d/simd_{kernels,native_rows}.spl` | | | | D1/D2/D8 | | D |
| `runtime/runtime_simd_dispatch.c`, `interpreter_extern/simd.rs` | | | | D2 | | D |
| `gc_async_mut/gpu/engine2d/{backend_software,compositor}.spl` | | | | D2–D6 | | D |
| `os/compositor/wm_core.spl`, `nogc_sync_mut/compositor/tile.spl` | | | | D6/D3 | | D |
| `os/drivers/virtio/virtio_gpu*.spl`, `nogc_async_mut/gpu/vulkan_icd_virtio.spl` | reads | | | | E1–E3 | E |
| design doc `…screen_backend_selection_and_shared_showcase.md` | ⚠ | ⚠B0 owns | ⚠ | ⚠ | | **already co-edited → 1.4** |

**Four true collisions** (1.2 ×2, 1.3, 1.4); the three `⚠lists/assumes/requests` rows are plans
naming a file they only read — fixable by wording. The brief's named risk areas are otherwise
clean: `src/os/compositor/*` splits A=factory / C=input+`compositor.spl` / D=`wm_core.spl`;
`src/lib/common/ui/*` splits B1=types / B8=catalog; engine2d + `runtime_simd_dispatch.c` are
D-exclusive; `virtio/*` is E-exclusive.

### 1.2 A5 vs E4 — the multiconfig evidence checker
Both claim `check_simpleos_multiconfig_live_evidence.spl` and
`simpleos_config_matrix.spl:594` (`ws_a:293-294` vs `ws_e:496`); both add fail-closed required
keys to the same array and both touch the verdict path.
**Resolution: E4.2+E4.4 land first** — E4.2 rewrites the existing `:145` device assertion into a
lane-keyed allow-list, a semantic change flagged as a lane blocker (`state.md:33-36`) and
explicitly landable ahead of E1–E3. A5 then *appends* its `simpleos_screen_<T>_*` rows and must
not re-derive `status_or_default`. Sequence: **E4.2/E4.4 → A5**.

### 1.3 `fb_backend.spl` / `browser_backend.spl` are unowned
WS-B §0.1 rows 7-8 say "owned by WS-A/WS-C"; neither WS-A nor WS-C lists either file. They are
the only real `impl RenderBackend for` sites (§3.1). **Resolution: assign to WS-A** as an
explicit *no-change-this-campaign* row, RenderBackend→ScreenHost migration filed as follow-on.
Unlisted is how two agents both edit a file.

### 1.4 Design doc already co-edited
B0 claims it exclusively (`ws_b:209`), yet it already carries `Correction (WS-A detail…)` (:18),
`(WS-C detail…)` (:78), `Escalation (WS-D detail…)` (:97), `WS-E verified` (:127).
**Resolution:** B0's residue is the §3 corrections (still wrong in the doc); all later edits via B0.

---

## 2. Interface contradictions

### 2.1 `HostInputEvent` payload — hard contradiction, blocks C1
B1, the declared sole definition site (`ws_b:265-268`):
`Pointer(x: i32, y: i32, button: i64, pressed: bool, wheel: i32)` / `Key(code: i64, ch: text, down: bool, mods: i64)`
WS-C (`ws_c:62-66`): `Pointer(x, y, dx: i32, dy: i32, button: i32, pressed, wheel)` / `Key(code: i32, …, mods: i32)`
Divergence: arity 5 vs 7 (breaks every positional constructor) and `i32` vs `i64`.
**WS-B is right on both.** `i64` matches `WmFsAppEvent.button: i64` (`wm_app_process_contract.spl:20`)
and crosses the WM file bridge and the C/PS-2 boundary without an ABI question. On `dx`/`dy`:
**no planned consumer reads them** — B2 derives drag from `_set_drag_anchor` (`ws_b:518,544`),
C5's `_route` never touches deltas (`ws_c:488-493`), and `ps2_mouse` maintains absolute clamped
x,y, so `Pointer.x/y` is authoritative; adding them violates "NEVER add unused code" and
invalidates B3–B6, which code against B1's published signature.
**Resolution:** B1's 5-field `Pointer` stands. WS-C deletes its §1 quote (already "for reference
only") and cites B1's file.

### 2.2 Wheel sign — hard contradiction
B1 (`ws_b:296-297`): "positive = content scrolls **down**, matching the sign of `dy` in
`widget_dispatch_scroll`". WS-C (`ws_c:70`): "+1 = scroll **up**", with C3 building a negation into
`host_pointer_event_from_ps2` (`ws_c:388-390`). If both land, PS/2 wheel scrolls the wrong way and
C3's bug-fix evidence looks right at the driver and inverted at the widget.
**WS-B is right:** `widget_hit.spl:120 widget_dispatch_scroll(root,w,h,px,py,dy)` is the sole
consumer and B2 passes `wheel * 24` straight in (`ws_b:513`); defining wheel against `dy` removes
the only place a sign can flip. **Resolution:** C3 drops the negation (PS/2 positive Z = wheel down
= positive `wheel`); its spec cases invert (`byte3=0x01 → +1`, `0xFF → -1`); C7 asserts end-to-end.

### 2.3 `mods` bits — agreement plus one omission
Identical bit assignment (shift/ctrl/alt/meta = 1/2/4/8), but WS-C adds **bit4 capslock**
(`ws_c:68`) which B1 has no constant for, while `Ps2Keyboard` tracks `caps_lock`
(`ps2_keyboard.spl:95`). **Resolution:** B1 adds `HOST_MOD_CAPS: i64 = 16`.

### 2.4 WS-A's factory return type vs WS-B's hosts — disjoint, and nothing bridges them
A2 returns `ScreenSelection{ backend: CompositorBackend?, shell: text }` (`ws_a:148-153`); WS-B's
hosts implement `trait ScreenHost` (`ws_b:305-311`) — disjoint traits, disjoint methods
(`display_backend_core.spl:7-18`). **No plan writes an adapter.** A2's claim that "`gui` becomes
reachable only once WS-B's `ScreenHost` gives `gui` an in-guest surface impl" (`ws_a:190`) has
nothing behind it — nothing in WS-B produces a `CompositorBackend`.
**Resolution: new task A6** (sonnet, dep A2+B3) owning `os/compositor/screen_host_bridge.spl`:
`fn screen_host_over(backend: CompositorBackend) -> ScreenHost`, rasterizing a `DrawIrV3Scene`
into `blit_pixels`/`present_rect`. Without it AC-1 and AC-3 do not meet.

### 2.5 B3's guest mode violates B7's own arch block
`ws_b:597-598` has `host_2d.poll_input` "guest mode: drains the WS-C input queue" — that queue is
`src/os/drivers/input/input_event.spl`. B7's PERMISSIVE block for `hosts/` denies `os/**`
("`os/**` stays denied even for hosts", `ws_b:833-838`). B3 cannot compile its guest path without
failing B7's own check. **Resolution: B3 is host-mode only** (script-driven queue); guest 2d input
belongs to C5 + the A7 screen app (§6.1). B3's brief drops the guest-mode line.

### 2.6 WS-D's present/damage change vs `present_scene` — no break, one required note
D3 (`ws_d:351-354`) redefines `present()` as a loop over merged dirty rects, preserving clear
semantics; `ScreenHost.present_scene(scene) -> bool` sits a level above and is unaffected.
**But** if B3 rasterizes the whole scene into a raw buffer each frame without marking damage, D3's
optimization is defeated in exactly the scenario D3 measures. B3's `present_scene` must write
through the marking ops (`mark_span_dirty`, `backend_software.spl:815`). **Add to B3's brief.**

---

## 3. Contradictory factual claims (verified against source)

### 3.1 "`RenderBackend` is never impl'd" — FALSE, and three documents repeat it
Claimed in `ws_b:23` ("**Zero `impl RenderBackend for` exists anywhere in the tree**", restated
`:321`), design doc `:47`, and `state.md:58`. Verified:
```
src/os/compositor/fb_backend.spl:133:      impl RenderBackend for FramebufferBackend:
src/os/compositor/browser_backend.spl:307: impl RenderBackend for BrowserBackend:
```
Both `use common.ui.backend.{RenderBackend}` (`fb_backend.spl:15`, `browser_backend.spl:16`), so
these impl the trait at `common/ui/backend.spl:22`. (An unrelated `trait RenderBackend` also lives
at `gc_async_mut/gpu/engine2d/backend.spl:61` with impls in `backend_cpu.spl:19`,
`backend_baremetal.spl:93`, `backend_intel.spl:141` — two live traits, one name; §6.4.)
**Consequence:** WS-B's *conclusion* (additive, don't rename) is strengthened — a rename now breaks
two compiling impls, not zero — but its rationale, its acceptance grep, the design doc and
`state.md` must be corrected by B0. **WS-B is right on the importer count (verified exactly 8),
wrong on impls.**

### 3.2 `FramebufferBackend` impls `RenderBackend`, not `CompositorBackend` — TRUE
`fb_backend.spl:108` / `:133`. WS-A (`ws_a:24`) and the design doc's correction (`:18-19`) are
right; the pre-correction text was wrong. `fb_backend.spl:20` still imports
`CompositorBackend, FbCompositorBackend`, so A2's "the fb arm needs an adapter" stands.

### 3.3 `InputEventQueue` is not a queue — TRUE, WS-C is right
`input_event.spl:226`: four counters (`key/mouse/touch/gamepad_count`) plus last-seen scalars, no
storage. WS-C's "it must be written, not merely rewired" (`ws_c:27`) is correct; the umbrella's
"revive `InputEventQueue`" understates it — it is a new class.

### 3.4 WS-D D-F8 "a real second implementation to delete" — FALSE
`ws_d:88-90` (escalated into the design doc at `:108-111`) claims `nogc_async_mut/gpu/engine2d/`
carries full `simd_kernels.spl` + `simd_provider.spl` **bodies**. Verified: **21** and **9 lines**,
entirely `export use std.nogc_sync_mut.gpu.engine2d.…`; the `gc_async_mut` one is 3 lines chaining
through `nogc_async_mut`. `grep -rn 'fn simd_blend_row' src/lib` → **exactly one** definition,
`nogc_sync_mut/gpu/engine2d/simd_kernels.spl:372`. D1's acceptance grep (`ws_d:193`) passes
*before* D1 runs.
**Resolution: D1 is near-empty.** Residue: (a) `gc_async_mut/simd_provider.spl` resolves direct to
`nogc_sync_mut` while `simd_kernels.spl` hops via `nogc_async_mut` — inconsistent path, same owner.
(b) Confirm which tree `backend_software.spl:21` actually resolves to before D2 measures anything.
Re-scope D1 to minutes; correct D-F8 and the design doc line.

### 3.5 Verified agreements
`ShowcaseSurface` = 3 variants (`showcase_catalog.spl:5-8`) ✓; `WmFsAppEvent` has no key/char/wheel
(`wm_app_process_contract.spl:17-23`) ✓; `widget_dispatch_scroll`/`_key` signatures
(`widget_hit.spl:120,311`) ✓; 8 `common.ui.backend` importers ✓.

---

## 4. Dependency-order problems + corrected critical path

1. **C5 depends on a file no plan creates** — "A2's screen app shell
   (`os/compositor/screen_app_2d.spl` per WS-A)" (`ws_c:471`). A2 produces only a `shell: text`
   key. → §6.1.
2. **C5's declared deps are incomplete** (C1, C3, A2 — `ws_c:509`). Its loop calls
   `self.host.poll_input()`, i.e. `ScreenHost` → also needs **B1, B3**.
3. **A5 cannot pass before WS-B lands.** A5 requires `screendump_distinct_colors > 1` for all four
   types (`ws_a:307`), but only `wm` paints today; `2d`/`web`/`gui` paint only once B3/B5/B4 (+A6)
   exist. → A5 also depends on **B3, B4, B5** (and E4.2, §1.2).
4. **D8 depends on A1** — D8's `screen_simd` rc.conf key is created by A1 (`ws_a:64,101`); D8
   declares only D2.
5. **Umbrella task IDs ≠ detail plan IDs for WS-D**: umbrella D1 = detail D2, umbrella D2 = detail
   D2.3, umbrella D5 = detail D8, umbrella D8 = detail D9. Two agents told "D1" do different work.
   → renumber the umbrella table before dispatch.
6. **Umbrella's critical path is wrong** (`B1→C1→C2→C5`, umbrella `:80`): C5 needs C3, and C7 needs
   C2+C3+C5.

```
tier 0 (no deps):  A1 · B0 · D0 · E1 · E4.2+E4.4 (fail-closed scaffolding)
tier 1:  B1 (opus, BLOCKS B2–B6 + C1) · A2 · D1 (re-scoped, §3.4) · E2
tier 2:  B2 B3 B4 B5 B6 (5-way) · C1 (opus) · A3 A4 · D2 (opus) · E3
tier 3:  C2 C3 C4 · A6 bridge (§2.4; needs A2+B3) · D3 D4 D7 D8(+A1) · B7
tier 4:  C5 (C1,C3,B3,A6,A7) · D5 D6 · B8 (B3–B7)
tier 5:  C7 (C2,C3,C5) · A5 (A3,A4,B3,B4,B5,E4.2) · E4 rows · D9 standing
```
**True critical path:** `B1 → C1 → C3 → C5 → C7` (AC-5/AC-6), with `A1 → A2 → A6/A7 → A5` close
behind and gated on B3/B4/B5. `D0 → D2 → D3 → D6` is independent. WS-E is independent except
E4.2 sequencing ahead of A5.

---

## 5. Duplicated work

1. **Mouse-wheel semantics defined twice** — B1 (`ws_b:266,296`) and C3 (`ws_c:388-390`),
   contradictorily (§2.2). → B1 owns semantics; C3 owns PS/2 decode + the three drop sites.
2. **`HostInputEvent` shape stated twice** with different fields (§2.1). WS-C already forbids
   itself from declaring it (`ws_c:55-58`); the risk is an agent coding to the quote. → delete it.
3. **Evidence-wrapper work** — A5 and E4 on the same checker and required-keys array (§1.2).
4. **`screen_simd` value set mismatch** — A1's accessor validates `auto|on|off` (`ws_a:101-102`),
   D8 specifies `auto|off|sse2|avx2|neon` (`ws_d:466`). A1 would reject `sse2`. → A1 adopts D8's set.

---

## 6. Unclaimed gaps

1. **Screen app shells.** Design §2.1 says the factory builds a `CompositorBackend` **+ screen app
   shell**; A2 returns only `shell: text` with nothing behind it, and C5 assumes
   `screen_app_2d.spl` exists. → **new A7**: `os/compositor/screen_app_2d.spl` (+ web/gui siblings)
   and the desktop launcher dispatch on `ScreenSelection.shell`.
2. **`CompositorBackend` ↔ `ScreenHost` adapter** → new A6 (§2.4).
3. **`SIMPLE_SCREEN_TYPE` has no host dispatcher.** A4 adds `screen_type_from_env_or()`
   (`ws_a:267`) but WS-B ships four separate mains with no entry point that reads the env and picks
   one, so AC-1's "host and guest select identically" is unmet. → a `main_showcase.spl` dispatcher,
   or A4 narrows its claim.
4. **`RenderBackend` deletion / two-trait name collision.** B1 defers it to "whoever owns the
   `ui.*` consolidation" (`ws_b:327-329`); nobody owns it, and §3.1 shows two live traits share the
   name. → file a bug, assign out of campaign.
5. **`fb_backend.spl` / `browser_backend.spl` unowned** (§1.3).
6. **Guest-side `web` is half-specified.** A2 marks it "partial — the HTML engine + net stack are
   host-side today" (`ws_a:189`), yet AC-2 needs all four types nonblank and A5 forbids green while
   any type is `skipped` (`ws_a:309`). The static-local-page fallback A2 sketches has no task.
   → give it a task, or declare `web`-on-guest a recorded evidence-bearing skip.
7. **`HOST_MOD_CAPS`** missing from B1's constants though PS/2 tracks caps-lock (§2.3).
8. **No plan owns the key-code vocabulary.** `Key(code: i64, …)` has three producers with three
   code spaces: C1's `ps2_key_code(k: Key)` ("stable numeric code", undefined — `ws_c:200`), C4's
   `sdl2_event_key_code` (SDL keycodes, `ws_c:443`), C6's Linux evdev codes (`ws_c:525`). Nothing
   normalizes them, and `showcase_core` does `if ch != "" then ch else _keyname(code)`
   (`ws_b:533`) — so non-printable keys render differently per host, breaking AC-4's
   byte-identical claim. → B1 owns a `HOST_KEY_*` canonical table; each producer maps into it.
