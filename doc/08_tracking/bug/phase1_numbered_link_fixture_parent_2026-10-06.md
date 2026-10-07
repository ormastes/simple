# Phase1 numbered link fixture parent

The rebuilt seed's numbered-closure spec ran five examples: four passed, and the checked directory-link case ended with a missing-file assertion. A separate filesystem probe showed secure_temp_dir_raw(".", ...) returning an absolute path containing /./. The strict snapshot boundary rejected that spelling and created no link. The failure output alone was insufficient to establish which earlier operations had succeeded.

The native temporary-directory API also preserves its supplied parent spelling. Correct the fixture to supply cwd(), so its private root meets the snapshot API's absolute-path requirement. Keep the boundary's dot-component rejection and all existing creation, resolution, readback, and cleanup assertions.

The selected previously failing original case passes on the prepared ac296d04dbb seed. The four passing cases were not re-executed. The enforcing watchdog recorded exit 0, quiescent 1, peak 1223612 KiB, and maximum sample gap 100 ms. Evidence is retained under /tmp/simple-numbered-link-fixture-repair and /tmp/simple-symlink-read-diagnostic. This is a Linux fixture correction, not a change to native or interpreter temporary-directory behavior.

Whole seed qualification and Phase2 admission remain pending.
