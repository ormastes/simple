# SOSIX ordinary text normalization

Status: source authored; all execution UNRUN. Selected contract: `doc/03_plan/utf8_internal_sosix_plan.md`. This port is separate from the prepared physical Char ABI and unresolved text-index selection.

## Actual boundary routing

The existing environment, host facade and stdio names now route through shared strict UTF-8 admission before ordinary tool processing. The codec remains `common.encoding.external_text`; no codec, charset detector, cache or runtime ABI is introduced. `text_boundary` is an implementation owner: its explicit external-value helpers are not re-exported from ordinary environment/process/console facades.

Environment checked getters preserve provider-reported missing versus present empty. A new nullable cwd thunk forwards the existing `rt_env_cwd` result without converting failure to `.` or empty success. POSIX bytes are admitted under an explicit strict UTF-8 policy, not detected as UTF-8. Unknown/Windows text providers return Unsupported pending a Unicode provider audit. Raw environment, directory and file APIs remain available in their existing low-level owners.

Command and all arguments are admitted, NUL-checked and bounded before a resolver can start. Bare names use an explicit `/usr/bin/which` or `/bin/which` path and the existing bounded process transport. Result output is validated before trim; successful empty/multiple-path/malformed output is an error. Explicit resolved paths bypass the provider's earlier raw bare-name trim. Existing process governor, timeout, truncation markers, spawn and V3/V4 ownership logic remain unchanged. No process owner rewrite or new process cache.

Console output encodes once to packed bytes and calls existing `sffi.fs.io_file_write_all`. Descriptors 1/2 are borrowed and never closed. Internal NUL survives the length-aware boundary. Native provider retries EINTR/partial writes; a failed write may have emitted a prefix and is reported as failure, never retried by SOSIX. stderr retains the legacy appended newline; failure before the newline can leave the already-written message.

## Failure compatibility

Checked APIs use `Result<..., TextIoError>` and `?`, preserving codec kind/byte offset. Legacy run maps checked errors to exit -1 plus diagnostic stderr; spawn maps errors to -1; Boolean environment mutators map errors to false. Existing nullable/text/void legacy APIs cannot carry an encoding error. Their documented adapter terminates with `panic` rather than returning false missing/empty/success. This is an explicit fatal compatibility path, not a new recoverable exception mechanism. New callers should use checked APIs. Existing raw APIs retain their original provider limitations.

## Bounds and remaining provider limitations

Each ordinary text input is at most16MiB before extraction. Arguments also have a65536 count and16MiB aggregate bound. Directory results are limited to65536 names/16MiB combined name bytes after the existing provider returns. Process capture requests at most16MiB per stream and validates the provider result; provider truncation/timeout diagnostic bytes remain part of the result. A result exceeding the outer16MiB admission bound fails explicitly.

These are logical boundary limits, not a total RSS/allocation guarantee. Initial environment/directory provider allocation happens upstream and is not bounded here. Provider nil can conflate absence with allocation/error; directory providers may report an empty list for some failures. This code preserves only distinctions actually supplied. Explicit UTF-16 conversions reuse existing foundation APIs; this port does not add arbitrary-encoding process transport or stdin/PTY support. Those providers remain a separate open part of the selected full plan.

## Source and runtime acceptance

Nine actual shared-boundary API cases, eleven real provider scenarios and one multi-mode native fixture are authored. No tests, compiler, helper, performance run or native fixture was executed. The native fixture requires an admitted compiler and exact `SIMPLE_SOSIX_TEXT_FIXTURE` path; absence is failure, not skip. Console byte capture, invalid resolver paths, provider timeout/truncation and invalid environment behavior need actual native execution. Existing cold/warm/maximum-RSS qualification remains required; no performance improvement is claimed.
