# Cross-target Cranelift signatures selected the compiler host ABI

Status: source repair; focused bootstrap regression PASS. Rebuilt Windows
Phase 2 execution and admission remain unverified.

## Observed failure

The Linux-produced Windows CI artifact `simple_stage2.exe` from main `817fef0`
has SHA-256 `3627e0dce493ff90805ddba998ce9dd62a2931c3a2f93432c44e38c112302c77`.
Running `--version` on Windows crashes during module initialization, before
the command can run. Preserved evidence is under
`D:/dev/simple/build/review/item5-gh-phase2-817fef0/`.

`string-args.log` stops in `rt_string_new_uncached_impl`, called by
`__module_init_app__build__targets__action_identity`. The string pointer is in
RDI and its length, 35, is in RSI (System V). The Windows runtime instead reads
RCX=2 and RDX=10700528. `crash.log` records the subsequent invalid read in
`msvcrt!memmove`. A PE header and successful linking did not establish ABI
compatibility or a runnable Phase 2 compiler.

## Owner and repair

The existing Rust bootstrap Cranelift code generator constructed a target ISA
for cross-AOT but selected function calling conventions through
`platform_call_conv()`, which inspected Rust's compile-time host OS. Runtime
imports, generated initializers, MIR functions, closure adapters and dynamically
declared calls therefore inherited the Linux host ABI even in Windows objects.

Cross-AOT signature owners now use their module ISA's `default_call_conv()`.
`build_mir_signature` requires that convention explicitly. The host-only
Cranelift SFFI default remains unchanged. This repairs an existing bootstrap
producer boundary; it does not implement application features in Rust or use
the seed as an application-test substitute.

The focused Rust regression `cross_target_signatures_follow_object_isa`
compiles x86-64 Windows and Linux objects on either host. It generates a MIR
function, an initializer calling the string runtime and an outlined body,
checks every declared signature against the target ABI, and checks emitted
COFF/ELF formats. Both targets are required so the host-based implementation
cannot pass merely by testing its native target.

## Qualification

Use an isolated Cargo target directory from `src/compiler_rust` so the checked-in
vendored dependency configuration applies:

```sh
cargo test -p simple-compiler --lib cross_target_signatures_follow_object_isa --offline -j 2
```

The initial invocation from the repository root failed dependency resolution
before compiling: it did not load the nested vendored-source configuration.
The corrected invocation is recorded separately. Neither a source review nor
an object-format test replaces rebuilding the Windows artifact and executing
`--version`, a real Hello compilation, and the resulting program. Preserve the
failed artifact and use fresh identities for corrected producer descendants.

The corrected Windows-host invocation passed: one test, zero failures, 4,285
filtered tests; the regression executed in 0.01 seconds. Both Windows COFF and
Linux ELF objects were emitted successfully. Log:
`D:/dev/simple-item5-cross-abi/build/review/cross-abi-cargo-vendored-test.log`.
The isolated target directory was
`D:/dev/simple-item5-cross-abi/build/cargo-cross-abi`. No broader test suite or
rebuilt Phase 2 executable was run for this repair.
