# Caret private credential native evidence

Default report: [summary.sdn](summary.sdn). One approved native owner-header and
unprivileged selfcheck compile/run passed for exact source
`b3b739b9ff4a8597d8400d972c16341d2797ba95`, UID 1000, compiler target
`aarch64-linux-gnu`, CPUs 0–4. No test was rerun. Foreign-UID and actual
PID-namespace-transition qualification remain **BLOCKED**. Simple facade/SSpec,
full runtime linkage and configured smux/Container binding remain **NOT_RUN**.
The injected origin-failure cases are labeled contract evidence.

## Historical artifact names

The original harness serialized JSON into a local file named `manifest.sdn`.
That filename was misleading. [manifest.json](manifest.json) preserves the
original bytes and SHA-256 exactly; it is an explicit historical JSON artifact,
not the default SDN report. Nothing in that evidence was rewritten.

The original [SHA256SUMS](SHA256SUMS) is also byte-preserved. Its paths are
relative to the original local evidence directory:
`build/caret-private-credential-b3b739b9ff4-20261107/`. In that list,
`manifest.sdn` corresponds to archived `manifest.json`; `source/...` identifies
the two immutable exported repository blobs; `credential_owner_test` identifies
the binary retained locally. The binary and duplicate source exports are not
committed. Their hashes, compiler/tool hashes, commands, limits and statuses
remain in the original manifest. The production header and fixture are normal
repository source files and can be compared against their recorded hashes.

[REPORT_SHA256SUMS](REPORT_SHA256SUMS) checks the files actually present in this
archive. It is separate from the unchanged original checksum list.

## Limits and warnings

Compile exit 0 in 0.154 seconds; execution exit 0 in 0.053 seconds. The approved
limits were 120 seconds/15 seconds and 128 MiB aggregate private artifacts;
actual artifacts totaled 115,568 bytes. The complete compiler and execution logs
are retained here. Two `-Wformat-truncation` warnings concern fixture path
buffers: its fixed generated path is at most 58 bytes within 512-byte arrays.
These warnings were not suppressed or used to justify rerunning a green check.
This evidence establishes neither full runtime qualification nor interactive
readiness or independent host/smux daemon behavior.
