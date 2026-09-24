# `simple test` on Windows silently runs specs on a STALE `bin/simple`, not the invoking binary

Date: 2026-09-01
Status: OPEN
Severity: High — verification lane integrity. Two sessions independently
produced false verdicts about an interpreter fix because of this (one false
"fixed" attribution dispute, one false REOPEN). See
`doc/08_tracking/bug/bytebuffer_struct_param_mutation_not_persisted_2026-09-01.md`
(second re-verification section).

## Defect

`src/app/test_runner_new/test_runner_single.spl` `find_simple_binary()`
resolves the child binary that actually executes every spec:

1. `SIMPLE_BINARY` env override — usually unset.
2. `rt_path_absolute("/proc/self/exe")` — **Linux-only**. On Windows it
   returns `C:/proc/self/exe` (no such file), so the invoking binary is never
   discovered in-process.
3. `cli_get_args()[0]` — is the subcommand (`test`), not a path.
4. Fallback: **`bin/simple`** — whatever was deployed there, however old.

Measured 2026-09-01 on `C:\Users\ormas\dev\simple`: invoking seed
`src/compiler_rust/target/release/simple.exe` (md5
`a544ad89978432578b7f185128339a80`, built same day) spawned children on
`bin/simple` (md5 `856e49ab0e499f5703f150491065960d`, **2026-08-24**). Every
`simple test` verdict on this box for the past week measured the Aug 24
binary regardless of what was built. The mismatch WARNING is printed
(`child binary ./bin/simple is NOT the invoking binary C:/proc/self/exe`)
but is buried in preamble noise and names a nonsense path; two sessions
missed it.

## Impact

- Any binary-baked fix (interpreter/Rust-side) appears inert to `simple test`
  until `bin/simple` is redeployed, while `src/lib/**` (source-read) changes
  ARE picked up — producing exactly the confusing "half the fix works"
  split observed in the ByteBuffer record.
- Workaround, verified: `SIMPLE_BINARY=<abs path to fresh binary> simple test ...`
  flips the child (`child binary: explicitly overridden by SIMPLE_BINARY`).

## Unblock condition / fix sketch

`find_simple_binary()` needs a cross-platform invoking-binary source. No
pure-Simple primitive currently exists (`current_executable_path` is imported
by `platform_measurement_observer.spl` from `std.nogc_sync_mut.io.sysinfo_ops`
but has no definition in the tree). Options: (a) have the driver publish
`std::env::current_exe()` into an env var before running interpreted apps and
read it in step 2; (b) back `current_executable_path` with a runtime extern
(register it — see the unbacked-extern ratchet) and use it here. Either way,
step 2 must stop being `/proc`-shaped on win32.

Not fixed in this pass (kept scoped; runtime-extern additions have their own
gates). Filed so the next false verdict is recognized in minutes, not
sessions.
