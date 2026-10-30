# Native completion failures discard child diagnostics

The frozen source86 runner's plain-red acceptance exited 1 and reported only
`native-test: normal completion evidence missing or invalid (exit 1)`.
Evidence: `D:/dev/simple-runner-archive-consumer-evidence-20261030/accept-plain-red-1793361178125019300`.
The launcher did not retain the raw child stderr and normal cleanup removed the
child executable. Therefore exit 1 alone does not prove an assertion panic or
the precise original diagnostic. That underlying failure still needs observation.

Source inspection establishes a separate reporting defect:
`make_native_completion_result_v1` receives captured stdout/stderr, but discards
both when completion evidence is missing/invalid and when a completed plain
program returns nonzero. Downstream private-session error transport already
preserves the result error as escaped diagnostic text.

The report owner now keeps the authoritative reason first and appends labeled
opaque child stderr and stdout excerpts. Each stream is limited to 1536 bytes
at complete character boundaries, leaving the combined message below the
4096-byte session diagnostic envelope. No log content determines completion,
classification, result counts, or success. Missing completion, early exit zero,
forged summary text and completed nonzero exits retain their previous verdicts.

Protocol regressions cover panic-marker preservation with forged pass counts,
stdout-only early exit, completed nonzero status, and bounded multi-byte output.
These are protocol inputs, not a claim to have observed the original panic.
Native execution and required broad checks are pending; no SSpec/native PASS is
claimed by this source repair.
