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
Actual C92 native plain-red execution now qualifies diagnostic retention:
`C:/dev/simple-runner-doctest-ntfs-evidence-20261030/accept-plain-red-1793375594192995200`.
The runner log retains the authoritative missing-normal-completion reason and
labeled stderr `panic: CALIBRATION_EXPECTED_plain_red_test`. The canonical
private frame `37c77764c98ab094275f9c70ab3e11aad51336539251df1afeb47db87500f13b.sdn`
binds the exact calibration fixture, child PID 27008, exit 1, timeout=false,
tree_reaped=true, and unchanged 0 passed/1 failed. Compile/execution durations
were 280885/148 ms. The outer tree was quiescent with no unexpected PIDs.
This is successful preservation of a real failing child's diagnostic, not
normal completion, a passing test, or evidence inferred from exit status alone.

Runner SHA256:
`7d9fb8780d252366d8c95b0f642ef6274cf5d41bd670afda1f642017de43d03a`.
C92 source manifest SHA256:
`cd9b9b35e147db081456b60269bfb66f3a1b79849638f82ab47754569e147532`.
That source includes this repair; admitted producer SHA256 is
`5dd85ea67087e063ae3a68ad0b282c82443e2ade6a178e0f10187fa93028260c`.
The release transplant preserves the newer `run_test_file_safe_mode` export;
its diagnostic logic and regression spec remain identical to the original fix.

Adjacent completion-verdict regressions and required compiler/lib/MCP/LSP plus
core/MCP smoke checks remain pending. No broad or SSpec PASS is claimed.
Because this changes a production `src/lib` owner, the additional library
checks apply; this is not an app-only change or an exemption from those gates.
