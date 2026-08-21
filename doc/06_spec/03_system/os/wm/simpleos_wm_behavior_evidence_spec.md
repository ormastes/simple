# SimpleOS WM Behavior and Visual Evidence

Status: executable manual, live-guest acceptance fail-closed. The mirrored
spec is `test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl`.

## Purpose and audience

This procedure is for SimpleOS WM implementers and release reviewers. It proves
the production owner's focus, close fallback, bounded damage, input routing,
composition, and restart behavior, then binds those host-fixture checks to a
separate live QEMU guest capture. Host pixels cannot substitute for guest
pixels, and a screenshot cannot substitute for semantic input/scene receipts.

## Preconditions

- An admitted pure-Simple runtime capable of running SSpec and the canonical
  SimpleOS WM evidence wrapper; Rust-seed and bootstrap-only artifacts are not
  accepted.
- QEMU, OVMF, QMP, image inputs, and framebuffer/input adapters required by
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- Enough space for four retained PPM frames, the evidence record, and report.
- No concurrent writer may use
  `build/test-simpleos-wm-hardening-behavior`.

## Operator workflow

1. Run the mirrored executable spec once with the admitted runtime.
2. Register three windows and verify focus stack order.
3. Close the focused window and verify deterministic stack-top fallback.
4. Admit current bounded damage and reject stale or invalid damage.
5. Route text through the focused production window and reject the stale
   target after focus changes.
6. Render overlapping runtime-created window pixels, preserve z-order during a
   lower-window damage update, then verify a focus raise changes the overlap
   pixel.
7. Commit input and framebuffer presentation, restart the WM, and verify stale
   generation work no longer matches.
8. Run the canonical QEMU owner and retain correlated input, scene,
   presentation-generation, framebuffer-readback, and QMP frame evidence.

## Scenario outcomes

| Scenario | Evidence class | Required outcome |
|---|---|---|
| Focus and close fallback | host-fixture | Stack is bottom-to-top; closing 30 focuses 20 rather than choosing by numeric ID |
| Damage admission | host-fixture | Current 80x60 region is accepted; stale generation and zero-width geometry are rejected with typed reasons |
| Input routing | host-fixture | Only the focused window route accepts committed text before and after a real focus change |
| Scene composition | host-fixture | The top window owns the overlap pixel; lower damage preserves it; focus raise changes it |
| Restart recovery | host-fixture | Old input and presentation identities are fenced and presentation state returns to zero |
| QEMU visual binding | live-guest | Wrapper exit 0; one PASS record; monotonic input-to-generation binding; four nonempty hash-addressed PPMs; fullscreen differs and restore matches baseline |

## Requirement scorecard

| Requirement | Coverage | Release meaning |
|---|---|---|
| REQ-017 | Six executable scenarios | Host behavior is supporting evidence; only the final live-guest scenario supplies SimpleOS visual acceptance |
| REQ-018 | Input, scene, frame, hash, and generation identities | No performance-budget claim is made here |
| NFR-005 | Bounded damage, input generation, restart fencing | The separate campaign spec owns 1,000-cycle and RSS evidence |

## Evidence and provenance

The live scenario writes only through the canonical wrapper to:

- `build/test-simpleos-wm-hardening-behavior/evidence.env`
- `build/test-simpleos-wm-hardening-behavior/report.md`
- `build/test-simpleos-wm-hardening-behavior/baseline.ppm`
- `build/test-simpleos-wm-hardening-behavior/fullscreen.ppm`
- `build/test-simpleos-wm-hardening-behavior/restored.ppm`
- `build/test-simpleos-wm-hardening-behavior/browser-event.ppm`

Acceptance checks artifact byte counts and SHA-256 identities, not file
existence alone. The evidence record binds the pointer input sequence to the
browser content-applied marker and matching presentation/delta generation.

No raster is checked into this manual as a fabricated example. Once a real run
is accepted, the retained PPM paths are the reviewable screenshot evidence.

## Findings and remediation

`BLOCKED[REQ-017-LIVE-GUEST]` is the only valid unavailable result. It includes
the failing wrapper exit or missing artifact and this resume contract:

`run scripts/check/check-simpleos-wm-fullscreen-evidence.shs with admitted pure-Simple image/runtime, QEMU+OVMF, QMP, and framebuffer input/readback`

Do not change BLOCKED to PASS, skip the live scenario, insert fixture images,
or accept host-compositor pixels as guest evidence. Repair the prerequisite or
production owner, rerun the single affected scenario, and retain the fresh
bundle.

## Compatibility and limitations

- The host fixture proves production Simple value/control paths but not a
  physical display, QEMU device delivery, or guest scanout.
- The live wrapper currently supplies the admitted x86_64 QEMU visual lane.
  AArch64, RISC-V, native-host, and physical-board rows remain separate required
  evidence and are not inferred here.
- EWMH and Wayland compatibility are outside REQ-017.
- Performance percentiles, the 24-hour soak, 1,000-cycle lifecycle campaign,
  and cross-architecture matrix remain owned by the hardening campaign spec.

<details>
<summary>Executable source</summary>

The complete executable source is the mirrored SSpec file named above. Keep
this section folded; operator steps and claim boundaries remain visible here.

</details>
