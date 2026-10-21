# Raw Result file measurement manual

Status: **AUTHORED / UNRUN**. Manual authored from the executable scenarios; spipe-docgen was not run.

Executable: `test/02_integration/compiler/verify/result_abi_raw_collector_spec.spl`.

1. Create an isolated temporary file containing known bytes, run the real collector, then clean up before assertions. Check the SHA-256 measurement, all five artifact roles, actual captured error payload, requested target, and unauthenticated/unchecked/open-binding statuses.
2. Create a real temporary file with a multibyte Unicode filename and require its known digest. Append NUL plus suffix in each of the five roles and require PATH refusal. Cleanup occurs before assertions.
3. Test empty and embedded-NUL text at every path position. A later invalid path must refuse before hashing an earlier nonexistent path.
4. Require missing file/provider failure and rejection of malformed/noncanonical digest text. Digest validation uses the production helper; provider unavailability is not simulated as a successful hash.
5. Measure real bytes, replace the test file, and measure again. The production comparator must reject drift. Equal measurements succeed only as raw consistency checks.
6. Reject missing or relabeled measurement rows; a structurally malformed observation cannot be treated as a successful consistency result.

The collector performs no shell fallback, subprocess, deletion, persistence, or logging. Hashes are point-in-time file measurements only. Pre/post equality is neither authentication nor an atomic file-descriptor pin. The actual executing compiler, runtime, probe, target, refinement proof, and checker authority remain unbound. No formal PASS or certificate is produced.
