<!-- codex-design -->
# SimpleOS Complete OS Hardening — GUI/WM Design

## Evidence desktop

```text
+--------------------- SimpleOS Desktop rev=42 ---------------------+
| launcher | Filesystem Evidence                         10:32:04   |
|          +-------------------------------------------------------+|
|          | [focused] FS Evidence                                ||
|          | x86_64  FAT32 PASS  DBFS BLOCKED  NVFS BLOCKED       ||
|          | receipt: build/evidence/.../evidence_receipt_v1.sdn  ||
|          | [Open blockers] [Capture]                             ||
|          +-------------------------------------------------------+|
|          +-------------------------------------------------------+|
|          | Window Manager Probe                                 ||
|          | W1/W2: OPEN FOCUS MOVE RESIZE REDRAW CLOSE           ||
|          | keyboard PASS  pointer PASS  frame=42 readback PASS  ||
|          +-------------------------------------------------------+|
| taskbar: [FS Evidence] [WM Probe] focus=W1 z=2                    |
+------------------------------------------------------------------+
```

## Required interaction flow

1. Create two process-owned windows and retain IDs plus service generation.
2. Click W1 title bar; prove focus/z-order and route a keyboard event only to W1.
3. Drag W1 through the shared WM action path and clamp geometry to the desktop.
4. Resize W2 through edge/grip; reject invalid/oversized geometry.
5. Occlude/expose and redraw; compare dirty render with full repaint.
6. Correlate scene revision, frame ID, scanout, framebuffer readback, and QMP capture.
7. Close W1, deterministically focus W2, restart WM, and prove no leaked resources.

Pointer capture begins only after an accepted hit test and ends on release, cancel, focus loss, owner death, or backend failure. Keyboard focus and pointer capture are separate. Escape cancels drag/resize without silently changing focus. Tab traversal follows semantic widget order, not z-order.

## Evidence and accessibility

Every window exposes semantic title, role, owner, focus, geometry, and status. Focus rings remain visible at high DPI. Screen readers consume the semantic tree, never pixels. Structured event/scene receipts are the oracle; screenshots are corroborating visual evidence.

- screenshots/goldens/diffs: `doc/06_spec/image/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec/`
- structured trace: `build/evidence/simpleos/wm/<target>/<environment>/<nonce>/wm_trace.sdn`
- framebuffer/QMP artifacts: the same nonce directory, hashed by `SimpleOsEvidenceReceiptV1`.

Physical-board capture is a separate path, never QMP: identify the board/CPU/display output and capture device, bind the flashed image and boot/download command, correlate serial/SSH scene/frame markers with HDMI/DP capture or framebuffer/JTAG readback, and hash every artifact in the physical `SimpleOsEvidenceReceiptV1`. A missing capture device or readback path is `BLOCKED`.
