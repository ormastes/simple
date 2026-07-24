# Agent Tasks: WM Glass Theme on Host and SimpleOS

## Shared Contract

Authority and interfaces are fixed: `ResolvedThemePackage`, derived
`ThemeRenderSnapshot`, existing `SimpleTheme` adapter, `WmChromeColors`,
`SharedWmScene`, `DrawIrComposition`, `Engine2D`, and canonical x86_64
`gui_entry_desktop.spl`. No lane may invent a registry or renderer.

Manual steps and fail-fast text are fixed by the system-test plan. Missing
helpers use `fail("wm glass theme evidence not implemented")` or `assert(false)`.

## Implementation Lanes

1. Package/snapshot lane: typed parsing, SHA-256 manifest/material identity,
   generator and drift checks.
2. WM/bootstrap lane: full projection, hosted startup and canonical SimpleOS
   generated-snapshot installation.
3. Web/Draw IR lane: package CSS wiring, computed-style/accessor repair,
   Engine2D glass lowering and focused regressions.
4. Evidence lane: extend canonical host, GUI/Web parity and QEMU wrappers;
   produce correlated semantic/capability/pixel/performance artifacts.
5. Spec/manual lane: executable SPipe scenarios, docgen, capture links and
   traceability review.

The three read-only design sidecars completed architecture, system-test and
GUI/evidence audits. Further lower-model sidecars may own only bounded lanes
above after checking worktree ownership.

## Ownership

- Merge owner: primary Codex agent in `/root`.
- Broad exclusions/done marks: primary only.
- Generated-manual reviewer: primary normal/highest-capability pass.
- Final production-readiness reviewer: primary highest available model after
  all sidecars finish and changes are merged.

## Merge Order

Package/snapshot -> WM/bootstrap -> Web/Draw IR -> evidence -> spec/manual.
Each lane supplies focused passing tests once; the merge owner resolves shared
types and verifies no concurrent unrelated work was absorbed.

## Continuation State — 2026-07-24

Authoritative integration worktree:
`/Users/ormastes/simple/build/worktrees/wm-glass-theme`, created from
`origin/main` at `3721a30541`. The shared root contains unrelated and
overlapping dirty work and remains read-only for this lane.

### Completed and retained

- Theme authority is `aetheric_dark`; package resolution, immutable
  `ThemeRenderSnapshot`, material/source hashes, generated bare-metal snapshot,
  package CSS, RGBA, ordered shadows, backdrop semantics, and named
  solid-material fallback are implemented.
- Canonical x86_64 SimpleOS evidence uses
  `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`,
  `engine2d_wm_frame_executor.spl`, OVMF, QMP input, and independent
  `pmemsave`; legacy `wm_entry.spl` is not evidence.
- The CSS-scan guest fault was reduced to Rust HIR result provenance:
  `text.split()` omitted `[text]`, while `trim`, `trim_start`, and `trim_end`
  omitted `text`. The owner fix and regression
  `inferred_text_predicate_does_not_reuse_unrelated_custom_owner` are present
  in current `main`.
- Retained pre-fix QEMU artifacts and exact diagnosis are recorded in
  `doc/09_report/wm_glass_theme_qemu_postfix2_2026-07-24.md` and
  `doc/08_tracking/bug/simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`.

### Active findings

| Lane | Current state | First unresolved boundary |
|---|---|---|
| Host production WM | SOURCE FIXED; recapture blocked by cycle cap | exact-current Stage 3 passed; bootstrap/theme/bridge/provider wiring is fixed, but the compiler containing the provider-link fix must be rebuilt before one fresh host capture |
| Host events | SOURCE PARTIAL; product proof pending | real key down/up and pointer move/button-edge receipts are retained; title-command/body-input remain unsupported because HostCompositor exposes no canonical API |
| Simple Web glass | SEMANTICS IMPLEMENTED, LIVE PROOF PENDING | current-source computed-style/Draw-IR/framebuffer proof has not passed; Chromium fixture timing is not Simple Web animation evidence |
| SimpleOS x86_64 QEMU | SOURCE FIXED, FRESH BOOT PENDING | rebuild exact current compiler, prove inferred-text relocation, then run one fresh canonical OVMF capture |
| SimpleOS ARM64 QEMU | FAIL; source wiring absent and runtime unproven | `arm64/gui_entry_desktop.spl` never installs the generated Aetheric snapshot, media lacks hosted package files, `ToggleTheme` is `pass`, and PL011 cannot receipt pointer or key down/up |
| Aggregate SSpec | FAIL-FAST BY DESIGN | `require_wm_glass_theme_evidence()` remains a real failure until host and required QEMU rows produce current-source evidence |
| Simple GUI theme handoff | SOURCE FIXED; product proof pending | resolved snapshot now reaches canonical widget Draw IR; 2 bootstrap-driver scenarios pass diagnostically |
| Simple Web theme authority | SOURCE FIXED; product proof pending | package CSS is now the final authority; 3 bootstrap-driver scenarios pass diagnostically |
| WM glass material projection | SOURCE FIXED; focused spec timed out | Draw IR retains durable identity/radius/border/shadows/backdrop request and named fallback; broad focused spec timed out at 120 seconds without assertions |
| Runtime theme switching | ABI BLOCKED; fail-fast system contract | numeric subscriber ports have no `IpcOutputPort`/send adapter, message schema, source identity, or delivery-failure policy |

### Current parallel ownership

1. Sidecar A: theme/CSS/WebIR/Draw-IR and Git-history audit, read-only.
2. Sidecar B: hosted production route and event/capture diagnosis, read-only;
   completed the split-theme finding above.
3. Sidecar C: x86_64/ARM64 canonical QEMU route, media/input/capture audit,
   read-only; completed and proved the ARM64 theme-install/input gaps.
4. Implementation sidecars: Web package CSS authority, WM material projection,
   and Simple GUI widget theme handoff, with non-overlapping source ownership.
5. `/root`: merge owner, host bootstrap regression/fix, compiler preflight,
   documentation, final high-capability review, sync and push.

### Next execution order

1. Focused current-source Rust HIR regression: COMPLETE. The corrected
   name-filtered run passed the intended test (`1 passed; 3346 filtered out`);
   the earlier `--exact` run was rejected because it filtered the test out.
2. Add red-before/green-after bootstrap regressions and:
   - install the resolved host package snapshot before backend/compositor
     creation through a hosted owner helper;
   - install the generated Aetheric snapshot before compositor construction
     through one freestanding-safe helper shared by x86_64 and ARM64 entries.
3. Build one exact-current pure-Simple bootstrap artifact and prove the CSS
   collision object routes inferred text to `_rt_string_starts_with` while the
   custom receiver still routes to `CustomPrefixOwner.starts_with`.
4. Run the focused host wrapper once:

   ```sh
   SIMPLE_BIN="$PWD/<exact-current-pure-simple>" \
     SIMPLE_BIN_SOURCE=wm-glass-theme-current \
     BUILD_DIR="$PWD/build/wm-glass-theme-host-current" \
     REPORT_PATH="$PWD/doc/09_report/wm_glass_theme_host_current_2026-07-24.md" \
     sh scripts/check/check-wm-production-fullscreen-evidence.shs
   ```

5. Only after the object preflight passes, run the x86_64 QEMU wrapper once:

   ```sh
   SIMPLE_BIN="$PWD/<exact-current-pure-simple>" \
     SIMPLE_BIN_SOURCE=wm-glass-theme-current \
     BUILD_DIR="$PWD/build/wm-glass-theme-qemu-x86-current" \
     REPORT_PATH="$PWD/doc/09_report/wm_glass_theme_qemu_x86_current_2026-07-24.md" \
     sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
   ```

6. Build/run the ARM64 canonical desktop after theme wiring:

   ```sh
   SIMPLE_BINARY="$PWD/<exact-current-pure-simple>" \
     SIMPLE_LIB=src SIMPLE_OS_BUILD_TIMEOUT_MS=900000 \
     "$PWD/<exact-current-pure-simple>" os test \
       --scenario=arm64-desktop-engine2d --log=off
   ```

   Extend the current RAMFB evidence owner to capture the canonical
   `arm64-desktop-engine2d` scene and explicitly report unsupported event
   semantics. Completion additionally requires a QMP-routable ARM input owner
   for pointer movement/button down/up and keyboard down/up; PL011 characters
   cannot satisfy that contract.
7. Replace the aggregate fail-fast helper only when it reads and validates
   production artifacts; then regenerate and review the manual.

### Admission rules

- A Rust seed, Stage 2/3 compiler used as a product runner, compatibility WM
  entry, source marker, screenshot without framebuffer provenance, synthetic
  event receipt, CPU mirror labeled as device readback, stale capture, or
  selector-free CSS rewrite cannot pass.
- Do not run QEMU before the focused compiler/object preflight is green.
- Each acceptance criterion is verified once per current source state, with at
  most three fix/verify cycles.
