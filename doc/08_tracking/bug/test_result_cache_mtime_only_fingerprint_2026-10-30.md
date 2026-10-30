# Test result cache served stale results after a same-second, same-size edit (2026-10-30)

Status: FIXED (this change)

## Symptom

`test/01_unit/app/test_runner_new/test_result_cache_spec.spl` passed 2/3. The scenario
"invalidates cache when dependency content changes without changing size" got
`result_status == 0` (fresh) after `dep_a.spl` was rewritten from `alpha` to
`omega`. It expected `-1` (stale).

## Root cause

`_dep_hash` in `src/app/test_cache_shared.spl` built the fingerprint from
`file_stat(path)` alone. That function returns the mtime in whole seconds. A
rewrite in the same second therefore produced an identical fingerprint, and the
cache kept serving the old pass/fail verdict. The same module also backs
`test_daemon/cache.spl` and `test_incremental_state_shared.spl`.

## Fix

Each path now contributes `mtime@sha256(content)` to the fingerprint, using the
runtime `rt_file_hash_sha256`. A missing path contributes `missing`, because
the runtime returns nil for a missing file. Old cache rows simply miss once.

Cost, measured with the same tree and the same seed binary, on 63 deps and 10
entries: 2.18 ms per entry before, 6.98 ms per entry after (about 76 us per
dependency file).

## Specs

- Reproducing: `test_result_cache_spec` "invalidates cache when dependency
  content changes without changing size".
- Generalization, in the same spec:
  - a same-size rewrite of the test file itself must invalidate;
  - an untouched entry must stay fresh;
  - a dependency that was missing at record time and appears later must
    invalidate.

  The fixed code passes 6/6. On the old code the two same-size examples fail
  whenever both writes land in the same mtime second, which is likely but not
  guaranteed.

## Follow-up (not done here)

A miss hashes the closure twice: once for `check_freshness` and once for
`record_*`. There is no per-run `{path: fingerprint}` memo, and dependency sets
overlap heavily. A cold full run therefore pays about 63 x 76 us x 2 per spec.
A memo would recover most of that. The long-lived test daemon would need to
invalidate it on file-change events.
