# Bootstrap Stage 2 backend object-path failure

## Status

Open. Reproduced after two intervening module-surface freeze defects were fixed.
The mandatory three-cycle fix/verify budget is exhausted; do not retry this
rollout without a fresh scoped session.

## Reproduction

```sh
env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 \
  --output=build/image-read-bootstrap-v3 \
  --strategy=normal --mode=dynload --jobs=half
```

## Observed failure

Stage 2 compiles and reaches bootstrap compiler sanity. The positional
hello-world frontend smoke parses and lowers successfully, then its native
compile fails with `backend object-path status 1`. The candidate is rejected;
seed fallback is correctly refused.

Primary evidence:

- `build/image-read-bootstrap-v3/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`
- `build/image-read-bootstrap-v3/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
- `build/image-read-bootstrap-v3/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`

## 2026-09-08 fix cycles

1. The native and Rust backend-plugin bridges called provider diagnostics only
   after success. Both now collect diagnostics after success or failure while
   retaining the primary status. The focused source contract
   `test/01_unit/compiler/backend/backend_plugin_failure_diagnostics_source_contract_test.shs`
   passes. A fresh `v4` run then exposed a separate module-surface failure.
2. `v5` replaced the staged-native-unsafe construction-dictionary `len()`
   check with the established materialized `keys().len()` boundary. It advanced
   to `frozen module surface lookup is incomplete`.
3. `v6` applied the same safe check to the rebuilt frozen lookup. Surface
   freeze, HIR, monomorphization, and MIR then completed, but native AOT again
   ended with `backend object-path status 1` and no diagnostic file content.

Latest evidence:

- `build/image-read-bootstrap-v6/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`
- `build/image-read-bootstrap-v6/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
- `build/image-read-bootstrap-v6/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`

The remaining failure is downstream of MIR and inside the selected backend
object-path session or publication path. No `simple-dynamic-aot-*` or
`simple-aot-diagnostic-*` directory remains under the evidence root or `/tmp`,
so cleanup completed (or the staging path never became observable). A next
session should add scalar stage/status diagnostics that do not depend on the
same file-writing path, then run one isolated cached sanity cycle.

## Impact

No admitted self-hosted runtime is available for compiling or executing the
image-to-Markdown feature tests. This was the third and final bootstrap
verification cycle for the feature session, so it was not retried.

---

## Re-verified 2026-09-13 — now the FIRST blocker, after the staging defect was fixed

This record is no longer behind another failure. The Windows/MSVC Stage 2 lane
reached it again today after a long chain of fixes, and it is now the frontier.

What changed since 2026-09-08, all landed on `main` today:

- Stage 2 link went from **33 unresolved externals to 0** (sqlite closure cut,
  `S_ISDIR`/`S_ISREG`/`__builtin_popcount`, four unimplemented `rt_file_*`
  externs implemented, and two Simple methods that were called but defined
  nowhere).
- The Stage 2 compiler is **built and runs** — `simple-bootstrap 1.0.1-beta.1` —
  and natively builds a hello world by hand (rc=0, exe produced).
- `diagnostic staging unavailable` is **fixed**: `rt_secure_temp_dir` was hitting
  `CreateDirectoryA`'s 248-char directory limit (`ERROR_FILENAME_EXCED_RANGE`,
  206) on a 258-char staging path; it now uses `CreateDirectoryW` with the
  extended-length prefix.

Evidence that this record's failure is what remains, and is distinct:

```
reason-len=30  ->  "diagnostic staging unavailable"   (before, now fixed)
reason-len=28  ->  "backend object-path status 1"     (now)
```

and the staging diagnostic no longer fires at all (0 occurrences of
`rt_secure_temp_dir:` in the smoke log), confirming staging now succeeds.

## What is still missing, and it is the same complaint as 2026-09-08

The reason delivered is still opaque: `backend object-path status 1` is a status
code with no message. `compile_aot_into_path` is handed a `diagnostic_path` to
write a reason into, and that file is either empty or unread — so the caller can
only report the number.

The staging defect above was solved in one run once the failing call was made to
say `GetLastError` and the path it tried. The same move is the obvious next step
here: make the backend write, and the driver surface, whatever it knows before
returning 1. Note the trap that cost time on the staging fix —
`rt_secure_temp_dir` has three byte-identical copies and only
`runtime_secure_staging.c` is the one that links, so instrument the copy that is
actually in the artifact and verify with `strings` on the binary rather than
assuming.
