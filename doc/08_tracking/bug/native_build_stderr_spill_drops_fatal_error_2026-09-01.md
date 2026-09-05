# native-build's stderr spill silently drops the real fatal error

**Date:** 2026-09-01
**Status:** OPEN — measured, not fixed
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
