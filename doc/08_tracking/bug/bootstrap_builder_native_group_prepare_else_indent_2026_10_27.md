# Bootstrap builder `else` indentation parse failure

**Date:** 2026-10-27
**Status:** Source indentation repair applied; frontend/object result unqualified after timeout
**DB registration:** PENDING

## Failure evidence

The pinned all-objects Phase2 `linux_main.spl` entry failed while parsing
`src/app/bootstrap_builder/native_group_prepare.spl`. Baseline compiler log:

`D:\dev\simple-all-objects-phase2-20261027\build\object-campaign\objects\c718ec0c9fbc4f25bdfe45181b7c4bc9\b112dbbb7c1e4ea190825abb8750747281021cc6b2cce9b1987c8e1c9c27e331\compiler.log`

The parser reports line 244:21: `unexpected token in expression: : ':'`.

## Diagnosis and proposed repair

At line 242, `val output_path = if ...:` begins an expression at 12 spaces of
indentation. Its then value is indented 16 spaces, and `else:` is also
indented 16 spaces. Aligning `else:` with the `if` expression at 12 spaces
restores the branch structure; the then and else values remain at 16 spaces.
Equivalent conditional expressions in neighboring bootstrap-builder files
use this alignment.

The approved repair dedented only the `else:` line by four spaces; the `if`
condition, then value, and both output strings are unchanged. The source file
SHA256 after this edit is
`3BDE8F0C7163F6839342537B84094B65351BF88356FFFA8325AF379E468DFFE6`.

## Validation receipt

Root's 180-second native-group-prepare diagnostic timed out before it reached
full parse or HIR. Receipt:

`D:\dev\simple-object-repairs-luna-20261027\build\object-repair\native-group-prepare-parser-smoke\collector.sdn`

The receipt records `reason=timeout`, `raw_status=124`,
`native_exit_status=124`, `cleanup_status=reaped`, and
`timeout_seconds=180`. The associated compiler log is
`D:\dev\simple-object-repairs-luna-20261027\build\object-repair\native-group-prepare-parser-smoke\compiler.log`;
its last progress line is `phase=surface_build`, 177/1366, at 179559 ms.
No object was produced. Parser/frontend and object validation are therefore
unqualified; this run does not establish parser success or failure. No further
build/retry was run. DB registration remains pending because the canonical
writer is blocked.
