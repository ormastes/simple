# macOS bootstrap live process qualification

# TODO: [bootstrap][P1] Run macos_process_live_spec.spl and the Phase2-produced native process-live fixture with absent and present stdbuf after the cold inventory memory blocker is fixed. Source fix and both test forms exist; the first focused compile stopped at 979,808 KiB after 25.4s and produced no artifact. Keep this open until real assertions pass with the admitted Phase2 compiler, recording peak RSS and elapsed time.

Owner: macOS bootstrap verification, coordinated with the Astra memory lane.

See `doc/08_tracking/bug/macos_bootstrap_capsule_scan_and_stdbuf_2026-09-21.md`
for the producer SHA, exact boundary, and test paths. The original eight-defect
platform cluster has separate, passing Stage 2 admission evidence.
