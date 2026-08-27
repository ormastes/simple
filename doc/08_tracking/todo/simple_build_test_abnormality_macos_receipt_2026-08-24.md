# macOS Process-Group Resource Receipt

Status: blocked pending a prepared macOS qualification host.

Owner: runtime/process provider maintainer.

Current source boundary: macOS has process-group/RLIMIT enforcement and legacy bounded execution, but the owned observed provider currently requires Linux pidfds and degrades to `ResourceEvidenceQuality.Unavailable`. Direct-child `ru_maxrss` byte semantics are already handled in the Unix receipt code.

Unblock work:

1. Permit the owned slot lifecycle to use start-identity plus `wait4`/`killpg` when pidfds are unavailable.
2. Retain direct-child CPU/max-RSS and sample descendant processes with documented process-only/sampled-tree quality.
3. Run direct-child, descendant, timeout, signal, and external-cancel fixtures on macOS.
4. Confirm every kill/wait path rejects `pid <= 0` and that unsupported counters remain unavailable.

Resume command on the macOS host: build the source-matched runtime and run `bin/simple test test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl` with the macOS platform rows enabled.
