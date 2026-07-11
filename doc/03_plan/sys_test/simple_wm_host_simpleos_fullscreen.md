# System Test Plan: Simple WM Host and SimpleOS Fullscreen

## Executable Specs and Manuals
| Spec | Manual | Purpose |
|---|---|---|
| `test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl` | `doc/06_spec/03_system/os/wm/simple_wm_host_fullscreen_spec.md` | Production host runtime, interactions, state restoration, captures, provenance |
| `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` | `doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md` | QEMU input-device path, live state, dynamic scanout, framebuffer captures |
| `test/03_system/os/wm/simple_wm_render_provenance_spec.spl` | `doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md` | Scene/content revision matching, semantic pixels, arbitrary text, DPI matrix |
| `test/03_system/os/wm/simple_wm_performance_spec.spl` | `doc/06_spec/03_system/os/wm/simple_wm_performance_spec.md` | Defined startup/mode/frame/input/RSS methodology and budgets |

Existing demo specs remain diagnostics but are removed from completion status. Placeholder no-report branches and boot-time `[wm-demo]` markers are deleted or changed to explicit incomplete/failure classification.

## Primary Manual Flow
1. `Launch the production WM in a host window`.
2. `Interact with internal windows and taskbar chrome`.
3. `Toggle the host surface to fullscreen and restore it`.
4. `Boot SimpleOS into its framebuffer desktop`.
5. `Validate captured pixels and backend provenance`.

## Runtime Oracles
- Host snapshot equality covers all window/taskbar fields before and after display transition; transition nonce/phase/geometry are asserted separately.
- SimpleOS target-window maximize/restore changes only expected fields; non-target state remains equal.
- Runtime-created long and Unicode titles/content mutate content revision and capture checksum; title ink stays bounded.
- Captures must exist, match producer PID/window/nonce/revision, have expected dynamic dimensions, be nonblank, and contain semantic top-lane/titlebar/window/taskbar regions.

## Folded Negative Matrix
Unsupported/denied/timeout/reordered fullscreen; replayed nonce; missing/stale/mismatched content artifact; seed/stale/wrong executable; corrupt/partial/stale report; missing/unverified/wrong-process capture; silent fallback; QEMU input failure/early exit/timeout; invalid scanout; hash mismatch; and every NFR budget breach.

## Traceability
REQ-1/6: host spec; REQ-2/6: SimpleOS spec; REQ-3/4: render-provenance spec; REQ-5/7/8: host + SimpleOS negative scenarios; NFR-1..7: performance spec; NFR-8: render-provenance matrix. Legacy `REQ-SIMPLEOS-WM-FULLSCREEN-*` identifiers map to REQ-2/5/6/7 and are superseded after new scenarios pass.

## Operator Manual Content
Each manual names prerequisites, exact wrapper command, environment classification, expected artifacts, cleanup, freshness rule (revision and capture timestamp), failure reasons, and platform/QEMU configuration. Primary flows show log/gui/statistics captures; negative/environment matrices are folded; plumbing is skipped.

