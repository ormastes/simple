# Feature Expert: SimpleOS WM QEMU Evidence Harness

## What this is
The QEMU-hosted test harness for SimpleOS window manager (WM) desktop, encompassing
image/disk construction, bootloader wiring, evidence-lane verification, and live
pixel capture for deterministic rendering validation.

## Source of truth
- **Harness admission:** Linked-worktree mode with version-probe seed detection
  (`fix 62e79e2d`) — gates stale binaries before QEMU spin-up
- **Evidence lanes:** Separate validation paths for different rendering backends
  (metal/vulkan/software), each with independent pixel-capture gates
- **Blocked on (x86_64, current):** `content-provenance-rejected` at first desktop
  frame — see § Session update 2026-08-04. The earlier parser ~100cps collapse
  (`doc/08_tracking/bug/native_build_parser_100cps_regression_2026-07-26.md`) is no
  longer the gating item on this lane; warm kernel native-build is ~45-75s.

## Code map
| File | Role |
|---|---|
| `scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs` | Widget showcase, Vulkan backend |
| `scripts/check/check-macos-vulkan-2d-live-evidence.shs` | 2D rendering, Vulkan backend |
| `scripts/check/check-macos-metal-2d-live-evidence.shs` | 2D rendering, Metal backend |
| `scripts/check/check-macos-vulkan-web-live-evidence.shs` | Web/HTML lane, Vulkan backend |
| `scripts/check/check-portable-compute-toolchains.shs` | Cross-platform compute stack |
| `src/os/hosted/hosted_wm_evidence.spl` | Evidence collection harness (pixel comparison, metrics) |
| `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | **Canonical x86_64 SimpleOS WM gate** (52 branches: build → disk → GRUB/OVMF → boot → readiness → QMP input → capture) |
| `scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs` | x86_64 readiness precheck (GRUB/OVMF discovery, `guide_gap`) |
| `scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs` | Hello-World window lifecycle lane |
| `scripts/os/build_browser_demo_client.shs` | Builds the in-guest browser-demo ELF staged onto the disk |
| `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` | arm64 attested desktop build (currently blocked, see below) |
| `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` | Freestanding runtime stubs + `BAREMETAL_HEAP_SIZE` |

Specs: Test-lane fixture verification (evidence gates in script suite above).

## Timeout environment knobs (2026-07-26)
- **Wall timeout must exceed worker timeout:** if harness wall-clock limit is shorter
  than worker process timeout, evidence capture silently fails
- **Per-lane configuration:** each evidence script accepts custom timeouts;
  diagnostic harness validates kernel boot completion before evidence lane spin-up

## Seed detection (admission gate)
The harness version-probes the `simple_seed` binary at startup:
- **Stale seed:** harness rejects and fails fast (do not spin QEMU against pre-stage4 binaries)
- **Missing seed:** linked-worktree mode detects via canonical release path
  (`bin/release/<triple>/simple_seed`)

## Live rendering evidence paths (2026-07-26)
- **Pass criteria:** nonzero byte count in output PPM (NOT file size)
- **Failure modes:**
  - Parser collapse → closure discovery stalls → no native code emitted → black pixels
  - Nil-self miscompile (LLVM lane) → guest crashes → empty framebuffer
  - Silent cache misses → stale binaries reused → outdated rendering logic
- **Workaround for stale cache:** forced rebuild via `--fresh-cache --full-bootstrap`
  (ensures re-run on fresh stage4 seed)

## Session update 2026-08-04 — gate ladder: build-death → full 4K desktop bring-up

Host: macOS arm64, x86_64 guest under TCG. The gate previously died at BUILD
(branch ~18 of 52). It now boots under OVMF pflash and reaches full desktop
bring-up at 3840x2160. Landed in `177754a3ee` + `2915bba5ec`.

### Repro
```
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple \
SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000 \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```
Timing on this machine: kernel native-build warm ≈ 45-75s (5 compiled / 726
cached); disk staging + GRUB EFI packaging fast; QEMU boot-to-desktop several
minutes under TCG. `SIMPLEOS_WM_READINESS_TIMEOUT_MS` is new (wrapper :883,
default 60000 unchanged — it replaced a hardcoded 60000ms loop). **TCG hosts need
~900000** for the 4K CPU-fallback layout; the default will time out.

### Five blockers root-caused and fixed
1. **Freestanding link fabrication.** Link refused: "would FABRICATE 3 symbol(s)
   not in the baseline: `rt_find`, `rt_native_cmp`, `rt_string_partition`". None
   existed anywhere in the repo — they are emitted by the *pure-Simple stage3*
   codegen for erased-receiver method calls (`bare_rt_redirect` class; the Rust
   seed binary has 0 hits). Real implementations added to `baremetal_stubs.c`
   (`rt_string_partition` = Python `str.partition` semantics; `rt_find`
   dispatches on receiver heap type; `rt_native_cmp` works for raw AND
   ENCODE_INT-tagged operands because ENCODE_INT is an order-preserving `<<3`).
   `S1(rt_array_sort)` fatal stub replaced with a real stable insertion sort.
   **Deliberately NOT re-baselined** into
   `config/freestanding_fabricated_stub_baseline.sdn` — a fabricated weak body
   returns 0 and silently corrupts every caller. Latent parity gap:
   `src/runtime/runtime_native.c` and the Rust runtime still lack all three.
2. **browser_demo client build (macOS).** `build_browser_demo_client.shs`
   hardcoded `CLANG=clang-20` (homebrew ships clang-22, keg-only) → "missing
   browser-demo compiler: clang-20"; and its ELF machine check via `od` produced
   a false "invalid browser-demo ELF" because BSD `od` emits a trailing
   address-only line. Fixed with a clang discovery ladder + `awk 'NR == 1'`.
3. **GRUB/OVMF discovery on macOS.** The readiness and hello-lifecycle scripts
   looked only for bare `grub-mkstandalone` and Linux OVMF paths. Homebrew
   provides `x86_64-elf-grub-mkstandalone` (keg-only, often off PATH; also at
   `/opt/homebrew/opt/x86_64-elf-grub/bin/`) and edk2 firmware at
   `/opt/homebrew/share/qemu/edk2-x86_64-code.fd` + `edk2-i386-vars.fd`. The
   canonical wrapper's discovery ladder was copied into both.
4. **Guest nil-receiver fault in font parsing.** After NVMe font load:
   `runtime error: field access on nil receiver`, `[fault] rip=0x8073034` →
   `llvm-symbolizer --obj=<kernel.elf> 0x8073034` named
   `lib__common__encoding__sfnt__parse_fvar_axes` directly. The
   value-position match `val table = match maybe_table: Some(value): value /
   None: return []` compiled to two discriminant-hash checks with a fall-through
   default loading the nil sentinel `0x3`. Statement-form matches on the same
   `Option<OtTable>` work — only the extract-into-`val` shape mis-discriminates
   on the freestanding lane. Fixed in `src/lib/common/encoding/sfnt.spl` with an
   Option-free flat scalar scan. Bug doc:
   `doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md`.
5. **Guest heap exhaustion.** Initial desktop bring-up alone (3 app surfaces +
   web-content font/style layout at 4K CPU fallback) hit
   `[PANIC] heap exhausted heap_off=0x1ffffa60 req=0x800 limit=0x20000000`. The
   baremetal allocator is a no-free bump allocator, so every render's
   allocations are permanent for the session. Stopgap: `BAREMETAL_HEAP_SIZE`
   512MB → 1GiB (warn 448MB → 896MB). Real fix remains frame-arena
   mark/release:
   `doc/08_tracking/bug/simpleos_bump_heap_no_free_interactive_session_2026-07-26.md`.

### Exactly where the gate stands now
Boots under OVMF → NVMe font chain read (1708408 bytes) → sfnt parse OK →
`[scanout-evidence] address=2147483648 width=3840 height=2160 generation=1` →
spawns Browser Demo / Hello World / Clang (`[desktop-gui]
process-owned-surfaces-ready count=3`, `launcher apps=15`) → `[wm-frame]
host-gpu-fallback reason=unavailable-or-readback-capacity width=3840
height=2160` → live web content layout → then:

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=guest-render-fault
[wm-frame] content-provenance-rejected window_id=3 status=engine2d_rendered backend=software fallback=none material= theme=aetheric_dark source=e13114ec...
[wm-frame] window-degraded window_id=3 reason=unresolved-or-duplicate-content
```

`material=` is **EMPTY** — this is a provenance *validation rejection*, not a
crash (no exception frames). The `guest-render-fault` label is the wrapper's
classification: `serial_has_production_fault`
(`check-simpleos-wm-fullscreen-evidence.shs:311`) matches
`^\[wm-frame\] content-provenance-rejected` as a production fault. The
provenance plumbing lives in `src/os/compositor/shared_mdi_framebuffer_scene.spl`
and `simple_web_window_renderer.spl`, which carried another session's
uncommitted edits (cf. `ac5fd76af0`), so this was **documented, not fixed**:
`doc/08_tracking/bug/simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04.md`.

**QMP input injection is the branch immediately after readiness — x86_64 WM
input delivery has STILL never been proven.** Do not claim input works on this
lane; the ladder has never reached that branch.

### Other lane facts
- **arm64 lane blocked upstream:**
  `build-simpleos-arm64-desktop-engine2d-attested.shs` fails
  `arm64_desktop_engine2d_attested_build_reason=rust-seed-or-debug-forbidden` —
  `resolve_compiler()` requires a non-seed
  `bin/release/aarch64-apple-darwin-macho/simple` and the deployed one fails
  admission. arm64 also still uses `-kernel`, which violates
  `.claude/rules/board-runnable.md`.
- **Doc gap the readiness script reports itself:** `guide_gap: true` — there is no
  `doc/07_guide/platform/simpleos/simpleos_x86_64_wm_qemu.md` (arm64 has
  `simpleos_arm64_wm_qemu.md`). x86_64 borrows `simpleos_dev_guide.md` §8.6/8.7.
- **Concurrent-session hazard:** the gate hashes its sources before and after the
  build window and fails `wm-simple-web-build-source-changed` if a peer edits
  `src/os/**` mid-build. This working copy is shared.
- **Grep trap:** searching serial logs for `fault` also matches "de**fault**-font"
  (`[rfm] at=default-font`). Always use `\[fault\]`.
- **Symbolizing a guest fault:** `llvm-symbolizer --obj=<kernel.elf> 0x<rip>`
  works directly on the SimpleOS kernel ELF. `llvm-nm | sort | awk` address-range
  hunting is unnecessary.

### Verification reality (2026-08-04) — what could NOT be checked
The related host-side specs **cannot go green on this host**. The deployed
`bin/release/aarch64-apple-darwin-macho/simple` is dated Jul 25 and its extern
registry lacks `rt_raw_i64_to_string`, so every spec importing
`src/lib/common/ui/native_scalar_text.spl` fails `semantic: unknown extern
function: rt_raw_i64_to_string`. It also predates grammar fix `023a60a05aa`
(trailing-comparison line continuation). Bug docs:
`doc/08_tracking/bug/deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md`,
`doc/08_tracking/bug/parser_trailing_comparison_line_continuation_2026-08-04.md`,
`doc/08_tracking/bug/stale_seed_binary_blocks_gpu_web_layout_specs_2026-08-01.md`.
`build/bootstrap/stage3/.../simple` **cannot substitute** — it is bootstrap-only
and has no `run` command. **Unblocking requires a real stage4 redeploy**, which
the user deferred. Consequence: the web/event gate
`check-wm-browser-event-routing-evidence.shs` fails closed at
`wm_browser_event_routing_reason=missing-simple-web-font-run-id` (a fail-closed
input precondition at wrapper :170) because its producer spec cannot compile.

## Related layer experts
- [os_compositor](../../layer_expert/os_compositor/skill.md) — WM frame composition + scene
  projection; owns the host/baremetal `dispatch_gui_*` parity and the provenance
  producers behind `content-provenance-rejected`
- [bootstrap](../../layer_expert/bootstrap/skill.md) — seed/stage2/stage3 redeploy gate
  (the stage4 redeploy that unblocks verification above)

## Related feature experts
- [interaction_input_routing](../interaction_input_routing/skill.md) — the input
  primitives behind the never-yet-reached QMP-injection branch
- [wm_gui_window_drawing](../wm_gui_window_drawing/skill.md) — frame/provenance
  contract that `content-provenance-rejected` enforces

## Update Rule
After harness admission logic, timeout behavior, evidence-lane additions, or seed
detection changes, refresh this skill with new configuration knobs and validation
paths.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`

## RV64 process-owned WM gate (2026-08-14)

The admitted RV64 gate is defined by
`doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`. A fixed rectangle scene,
string-only GUI stub, serial WM marker, or nonblank QMP image alone is
diagnostic. PASS requires a live process-owner PID/liveness receipt correlated
to the compositor's first presented frame after Sv39, PID1, network, and
production SSH readiness. Final manual/evidence review remains root-owned.
The producer and boot wiring, including byte-zero WM/Window IPC framing over
the owned copied transport, are source-integrated. TODO809 remains open only
for admitted focused/live execution: retain authenticated sender PID,
PID/liveness, scene and presented revision, positive scanout generation, and
QMP framebuffer metadata/hashes, then compose that evidence through TODO806.
The terminal-only WM resource checks are source diagnostics, not a retained
PID/frame receipt. The checker-loaded system SSpec currently segfaults before
its scenario result, so rerun the focused WM ledger only after TODO667 and
retain its outputs with the Stage 4 provenance.

The authoritative redo plan assigns WM four exclusive focused logs and starts
it only after the admitted Stage 4 and accepted IPC/VFS receipts exist. It may
run alongside boot-owner, SSH, and manual rows, but it must not start a second
live guest: the primary RV64 owner alone runs the combined port-2222/QMP row.
The earlier reachable WARN integration is a source handoff, not AC-5 or AC-10.
The production entry now keeps the accept/WM loop alive after the first
presented frame instead of returning from the daemon, and later accepted SSH
sessions remain subject to terminal and accept-resumed validation. This is a
source correction only until the admitted focused and live rows pass.

Historical cycle 3 published Stage 2 (binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`).
Host `earlyoom` then terminated Stage 3 at 41,394 MiB RSS on a no-swap host
with less than 10% free memory; exit 143 followed 5.4 seconds later. That parent
predates the complete snapshot provider. TODO666 is open/actionable: the M0
draft was reverted, resume-only durable sinks remain, and full-bootstrap
wiring plus admission-grade supervisor/provenance must still land before a
fresh current-HEAD Stage 2 and one instrumented Stage 3 run in a fresh session;
the interrupted high-water mark is not a proved RAM requirement. TODO667/A2
remains gated; no Stage 3/4, deploy, essential-smoke, or rollback evidence exists.

P1c IPC service transport is shared with the WM path: copied traffic is
selected only by `IPC_COPIED_SERVICE_TAG`, and syscall 18 permits the recorded
owner alone to revoke an endpoint. The VFS close watermark and SOSIX named-VFS
convergence are kernel/service details, but they must be included in B's
post-TODO667 focused retained ledger before WM consumes IPC evidence. They do
not substitute for authenticated sender PID, PID/liveness, revision, scanout,
or QMP evidence, and TODO806 remains the combined runtime blocker.
