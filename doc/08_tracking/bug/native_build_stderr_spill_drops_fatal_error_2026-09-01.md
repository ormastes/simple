# native-build's stderr spill silently drops the real fatal error
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-01
**Status:** SUPERSEDED — measured, not fixed
**Site:** `src/app/cli/native_build_main.spl` (~lines 280-330, the truncation/spill path)

## Symptom

On a large module closure, `native-build` truncates worker stderr and spills the
full text to a file. It then **reports a byte count that does not match what it
actually wrote**: a run announcing `413555 bytes saved` left only `211505` bytes
in the spill file and in the head/tail excerpt.

The bytes that go missing are the ones that matter. The fatal error is emitted
LAST, so on a closure large enough to trigger truncation the actual cause is
exactly what gets dropped, and the build reports failure with no usable reason.

## Why this keeps costing time

This is the **third** swallowed-diagnostic defect found in this area in one day:

1. The Stage 2 sanity gate hashed the frontend-smoke log into its evidence file
   and then `rm -f`'d it, so a failure reported `frontend_status=1` with zero
   error text, ever (fixed, `a927aac3dc3`).
2. `head -c 65536` captured the FIRST 64 KB — all clang-cl warnings — and never
   reached the error at the end (fixed, `a53e5c2f2ba`).
3. **This one.**

Separately, `clang-cl` (like `cl.exe`) writes diagnostics to STDOUT, not stderr,
so a fourth path was capturing the wrong stream entirely (fixed, `c4f9781509c`).

Each of these turned a one-line diagnosis into a manual reproduction.

## Workaround in use

Bypass the wrapper and drive the worker directly, which does not truncate:

```
bin/simple.exe run src/app/cli/native_build_worker.spl <args>
```

This is how the MCP/lint/test-runner closure failures were actually diagnosed.

## Suggested fix

Make the spill path write-then-verify: after writing, stat the file and report
the ACTUAL byte count, and fail loudly if it differs from the intended length.
A diagnostic path that silently writes less than it claims is worse than one
that does not write at all, because it looks like it worked.

Prefer keeping the TAIL when truncating (the fatal error is last), consistent
with the fix already applied in `a53e5c2f2ba`.

## Unix impact

The defect is in path/size handling, not platform-conditional code; the same
truncation logic runs on Linux and macOS. The earlier hardcoded-`/tmp` spill
bug in this same function (fixed, `15523fad2c4`) was Windows-only, but this
byte-count mismatch is not.


---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED

The truncation/spill path in `src/app/cli/native_build_main.spl` (`eprint_bounded`,
lines ~598-677 at release tip) no longer has the reported defect:

- The spill writes the FULL untruncated stderr via `file_write(spill_path, output)`
  and reports `output.len()` — the announced byte count and the written text are
  the same string, so the 413555-announced/211505-written mismatch is structurally
  gone (src/app/cli/native_build_main.spl:658-659).
- Before the head+tail view is printed, EVERY diagnostic line in the full stream is
  re-emitted (`native_build_collect_diagnostics`, lines 583-596, 664-671), so the
  fatal error — emitted last — survives even if it falls in the dropped middle.
- The head+tail view keeps the TAIL (`head_len = OUTPUT_LIMIT/2`, lines 672-676),
  matching the fix direction requested here and in a53e5c2f2ba.

Fixing commit on the release tip: 820631c6e5c7 (merge of PR #7545
`work/tcp-spill-signedness-20261107`, 2026-11-07) — blame and `-S` pickaxe both
place the full-spill + preserved-diagnostics mechanism at this commit.

Seed-smoke verification (2026-11-11, seed 0791c2b7f4a7, interpreter mode):
`bin/simple.exe test test/01_unit/app/cli_native_build_main_contract_spec.spl
--mode=interpreter --no-cache` — the spill-related case "routes the
worker-failure relay through the unambiguous stderr_write" PASSED. (Note: 11 of
17 content-matching cases in that spec fail on unrelated source regions —
VHDL/simpleos text drift on the release tip, pre-existing, not this bug.)
