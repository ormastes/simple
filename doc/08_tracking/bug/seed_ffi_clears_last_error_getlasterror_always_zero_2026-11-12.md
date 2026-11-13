# Seed FFI clears the Win32 thread last-error before each extern; GetLastError always reads 0

Status: OPEN. Found 2026-11-12 by direct probe on Windows 11 (Git Bash), phase-2
product-queue lane, worktree at `origin/release/1.0.0`, seed binary
`bin/simple.exe` copied from the main repo.

## Symptom

Every `GetLastError()` call made from Simple code through the seed's extern
dispatch returns **0**, even immediately after a failing Win32 API:

| probe | result |
|---|---|
| `GetFileAttributesW("C:/definitely-not-exists-zz/leaf.sdn")` | attrs = 0xFFFFFFFF (INVALID), `GetLastError()` = **0** (expected 2/3) |
| `CreateFileW(same, OPEN_EXISTING, ...)` | handle = -1 (INVALID), `GetLastError()` = **0** (expected 2/3) |
| `CloseHandle(-1)` | returned 1 (expected 0 + ERROR_INVALID_HANDLE) |

Measured in probe specs calling the same
`std.nogc_sync_mut.io.path_identity_abi` externs the product uses.

## Where

`src/compiler_rust/compiler/src/interpreter_extern/windows_abi.rs` — the
`"GetLastError"`, `"GetFileAttributesW"`, `"CreateFileW"`, `"CloseHandle"`
dispatch arms call the real windows-sys functions with no wrapper that
should disturb the thread last-error. The observed (attrs=INVALID, error=0)
pair is impossible on real Windows unless something clears the thread
last-error between the failing call and the `GetLastError` call. The seed's
extern trampoline evidently clears the last-error before each extern
invocation (a common "fresh error" FFI policy), which makes `GetLastError`
itself unfalsifiable: it is always observed as 0.

The pure-Simple self-hosted binary is not present in the phase-2 lane
environment, so every phase-2 spec runs under the seed and observes this
behavior.

## Impact

Any Simple code that distinguishes Win32 failure modes via GetLastError is
blind under the seed. Concrete victim:
`std.nogc_sync_mut.io.path_identity._path_entry_observe` treated
INVALID_ATTRIBUTES + error-not-in-{2} as `PATH_ENTRY_INDETERMINATE`, and the
scv db store-scope validators (`db_local_path_scope` in
`src/app/scv/db/local_store.spl`) fail-closed that to `SCVDB_STORE_SCOPE` for
every nonexistent `.sj`/`.scv`/store directory — walling off ~20
`scv_db_*_spec.spl` fixtures on Windows.

## Workaround landed (product-queue pass 2026-11-12)

`_path_entry_observe` (Windows arm) now accepts error 0 alongside
ERROR_FILE_NOT_FOUND (2) and ERROR_PATH_NOT_FOUND (3) as observed-absence
proofs. Under a correct FFI the strict behavior is unchanged (real access-
denied etc. still fail closed); under the seed FFI, a genuinely
access-denied path is indistinguishable from not-found and reports absent —
the caller's parent-identity re-check in `path_entry_present` still catches
hostile parent replacement.

## Proper fix (not done here)

- Seed: stop clearing the thread last-error before extern calls (or at least
  exempt `GetLastError`), then rebuild the seed binary.
- Longer term: stop hand-rolling GetFileAttributesW in Simple; route
  no-follow existence probes through the C runtime (`rt_dir_is_real_no_follow`
  / `rt_file_is_regular_no_follow`) which already implements the Windows
  contract in tested C (`src/runtime/runtime.c`).

## Repro

```
# in a clean worktree at origin/release/1.0.0 with the phase-2 seed binary:
./bin/simple.exe test test/02_integration/app/scv_db_local_store_it_spec.spl --timeout 300
# before the workaround: every example fails "called unwrap on Err: SCVDB_STORE_SCOPE"
```
