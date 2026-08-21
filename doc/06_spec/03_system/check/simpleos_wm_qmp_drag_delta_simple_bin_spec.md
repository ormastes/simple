# SimpleOS WM QMP drag-delta Simple binary contract

Mirror of `test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl`.

The executable SSpec verifies decoded PS/2 drag packets reach real lifecycle geometry, the launcher selects a self-hosted Simple binary and records its provenance, and an explicitly selected Rust seed is rejected before QMP launch.

The spec validates source and launcher contracts; it is not itself a recorded interactive QMP drag session.
