# Deployed self-hosted `bin/simple` SEGVs on every `native-build`: `env_set` miscompile

Precisely root-caused by Lane LAUNCH-OS-RISCV via gdb. This is why `bin/simple`
(the deployed pure-Simple self-hosted binary) is unusable as the default tool and
why every `native-build` through it crashes.

## Symptom

Any `bin/release/x86_64-unknown-linux-gnu/simple native-build ...` (the
`bin/simple` symlink target) SEGVs immediately — on **both** llvm and cranelift
backends, even for trivial input. The crash is a glibc `setenv` on a garbage
pointer, not anything in the compiled program.

## Root cause (gdb backtrace)

```
__strlen_avx2
  ← __add_to_environ(name="SIMPLE_OS_LOG_MODE", value=0x12)
  ← rt_env_set
  ← io.cli_ops.env_set
  ← ...cli_native_build
```

`cli_native_build` calls `env_set("SIMPLE_OS_LOG_MODE", log_mode)`. The deployed
self-hosted compiler miscompiles the SECOND argument: instead of the string
`"on"` it passes the raw small integer/garbage pointer `0x12`, so glibc's
`__add_to_environ` calls `strlen(0x12)` → SIGSEGV. So the compiler never even
reaches codegen for the user's program — it faults in its own CLI setup path.

## Scope / which binary

- BROKEN: `bin/release/x86_64-unknown-linux-gnu/simple` (a bad redeploy) — the
  `bin/simple` symlink. Also note `bin/simple` currently identifies itself as the
  Rust **seed** ("seed only" warning) in some states; either way the deployed
  default tool cannot `native-build`.
- WORKING: `src/compiler_rust/target/bootstrap/simple` — the Jul-13 llvm-capable
  bootstrap seed. All SimpleOS kernels in the launch-sanity lanes (x86_64,
  aarch64, riscv64/32) were built with THIS, not `bin/simple`.
- The fresh Rust *release* seed is NOT a substitute: it lacks the llvm backend
  and regresses (`cannot cast array to i64`).

## Impact

- The CLAUDE.md default ("all tooling runs on the self-hosted `bin/simple`") is
  not currently satisfiable for `native-build`.
- Blocks every launch/build path that shells out to `bin/simple`, and the
  in-guest self-hosted redeploy (#99). Downstream smokes that need the
  self-hosted backend (rv64 display smoke → `freestanding_runtime.c`/`boot_main`;
  riscv RTL Linux smoke) are blocked here too.

## Fix

Belongs in the pure-Simple compiler's argument lowering for `env_set` (the
string arg is dropped/replaced by an integer/tag value in this call site) — an
ABI/boxing miscompile, same family as the other deployed-redeploy defects.
Requires a compiler fix + a clean redeploy of `bin/release/.../simple`; it cannot
be worked around in userland. Until then, use
`src/compiler_rust/target/bootstrap/simple` for `native-build`. Gate the fix on
`bin/simple build bootstrap` + `bin/simple test`, not a probe.

## Verification handle

`env_set("SIMPLE_OS_LOG_MODE", "on")` reached from any `native-build`; a fixed
binary passes the real `"on"` string (no `strlen(0x12)`). Evidence:
launch-sanity `scratchpad/launch_riscv_recover/gdb_bt.txt`.
