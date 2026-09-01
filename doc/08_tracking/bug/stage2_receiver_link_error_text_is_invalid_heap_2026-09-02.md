# Stage 2 receiver probe: the MSVC link error message is a corrupted heap handle

**Date:** 2026-09-02
**Status:** OPEN
**Severity:** HIGH — destroys the diagnostic for the only gate blocking Windows Stage 2 admission

## Symptom

Stage 2 **builds cleanly** — 818 compiled, 0 cached, 0 failed, 105,879 KB `simple.exe`
via clang-cl, 624.7s compile + 33.3s link = 658.0s — and is then **rejected**:

```
reason=stage2-struct-receiver-failed
probe_exit=1
```

The receiver probe log (`stage3/x86_64-pc-windows-msvc/stage2-receiver.log`, 85,010 B,
line 902) ends with:

```
error: in-process native-build: Bootstrap LLVM link failed
  (input=.../bootstrap-stage3-route-guard.app.cli.bootstrap_main.o
   output=.../bootstrap-stage3-route-guard):
  Linking failed: Windows MSVC linking failed: <invalid-heap:0x1e9548829b1>
```

## The defect

**`<invalid-heap:0x1e9548829b1>` is not a linker message.** It is what the runtime
prints when a `text` handle does not reference a valid heap string. The linker's actual
error text — the one fact needed to fix this gate — is **destroyed** before it is
printed.

So the reported reason for the rejection is unknowable from the log. Every prior
investigation of `stage2-struct-receiver-failed` has been reasoning about an error
message that was never real.

## Why this matters beyond the bootstrap

This is the same corruption family as the two miscompiles fixed on
`session/text-compare-and-toint-miscompile-2026-09-01` (PR #269), where a tagged word
was consumed as if it were a value:

- `.to_i64()` / `.to_int()` on a text receiver compiled to a compare on the raw handle;
- text `<` / `>` / `<=` / `>=` compiled to `icmp` on allocation addresses.

Here the same class shows up in **error-message construction on a failure path**, which
is the worst place for it: the defect only manifests when something else has already
gone wrong, so it converts every such failure into an undiagnosable one.

## Evidence

- `stage2-rejected/x86_64-pc-windows-msvc/rejection.env`
  — `status=rejected`, `reason=stage2-struct-receiver-failed`,
  `candidate_sha256=3ed5dbf6db8bc215f09de85bb174c455b2aab452283c11bd66ad6e10c6abe66e`
- `stage3/x86_64-pc-windows-msvc/stage2-receiver.env`
  — `status=fail`, `probe_exit=1`,
  `candidate_sha256_before == candidate_sha256_after` (the probe did not mutate the
  candidate), `probe_log_sha256=ec28d72c699fc20ed1775b353f243b8e82d8bf3cfeb95b8e41bf121d476c418a`
- `stage2-native-build.log` tail confirms the build itself succeeded.

Note the probe reached the link stage normally: `[bootstrap-real-llvm] count 4`,
`[llvm-tools] llc-done`, `llc-object`, `read-bytes` all completed. Only the final link
failed, and only its message is corrupt.

## What must happen next, in order

1. **Recover the real linker error.** Do not attempt to fix the link until its actual
   text is visible — the current message carries no information. Options: capture the
   linker's stderr/stdout directly at the call site rather than routing it through the
   corrupted `text`, or print the raw bytes before they are wrapped.
2. **Then** diagnose the underlying link failure with a real message in hand.
3. **Fix the message corruption itself** as a separate change — an error path that
   destroys its own diagnostic will keep doing so for every future failure.

## Related

- PR #269 — the two text-handle miscompiles (`.to_i64()`, relational compares).
- `check-stage-log-diagnosable.shs` previously pointed at `stage2-native-build.log`
  instead of `stage2-receiver.log`, which is why this failure was reported as
  UNDIAGNOSABLE; that misdirection is fixed, and it is what made this log readable at
  all. The guard now correctly reports the stage said why — but *what* it said is this
  corrupted string.
- Same family as the four diagnostic-swallowing defects found 2026-09-01
  (phase-3 discarded diagnostics; `head -c` truncating failure logs to their useless
  first bytes; `2>nul` in the MCP wrapper; MIR errors dropping spans).

## Not yet established

- Whether the corruption is in the linker-invocation wrapper, in the error propagation,
  or is a further instance of the tagged-word class fixed in PR #269.
- Whether a binary built **with** PR #269's fixes still shows it. The candidate here
  (`3ed5dbf6…`) predates that verification.
