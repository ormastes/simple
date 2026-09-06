# Pure-Simple native MCDP focused check/test SIGSEGV

## Status

Root cause captured.  The frozen executable is internally ABI-incoherent:
its compiled frontend caller uses the current four-word `rt_env_set`
`(key_ptr, key_len, value_ptr, value_len)` contract, but its linked
`rt_env_set` definition uses the obsolete two-pointer `(key, value)` contract.
Do not run either reproducer again against this executable.  Produce a fresh,
atomically source/runtime-matched pure-Simple compiler and run the failed
standalone check once.

## Frozen evidence

- Source revision: `76193ab4953a3157e7d6d211f2bc10159107f026`
  (`docs(mcdc): record performance hardening evidence`).
- Candidate executable:
  `/mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple`
- SHA-256:
  `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
- ELF build ID: `545d912cac46001892de0d9959e6b0b92497f2b9`.
- Size: 42,477,824 bytes; inode 2259895; mtime
  `2026-08-11 22:10:09.323921115 +0000`.
- Host/target: Linux x86-64, pure-Simple release executable, not stripped.
- Kernel evidence, first attempt at 2026-08-22 05:54:00 UTC:
  PID 2967971, SIGSEGV read at address `0x11`, instruction pointer
  `libc.so.6` ELF offset `0x18b95d`.
- Kernel evidence, second attempt at 2026-08-22 05:54:07 UTC:
  PID 2968490, SIGSEGV read at address `0x1b`, the same libc offset.
- The installed libc debug map resolves offset `0x18b95d` to
  `__strlen_avx2` (`strlen-avx2.S:76`).
- Both invocations returned shell status 139.  Apport retained no matching
  report or core, and no command transcript was retained under `build/` or
  `/tmp`; therefore there is no trustworthy caller frame.

## Fresh-session symbolized capture

A fresh goal turn made exactly one diagnostic rerun of the standalone `check`
operation under GDB.  The frozen SHA-256, build ID, size, inode, and mtime all
matched the identities above before execution.  The process again reached
`Checking test/01_unit/compiler/driver/native_mcdc_transport_spec.spl...` and
then stopped in `__strlen_avx2`.

The retained stack is:

```text
#0 __strlen_avx2
#1 __add_to_environ(name="SIMPLE_BOOTSTRAP_EXPR_COUNT", value=0x1b,
                    combined=0x0, replace=1)
#2 rt_env_set
#3 0x1
#4 frontend__core___AstExpr__nodes__expr_count_set
#5 frontend__core___AstExpr__nodes__expr_reset
#6 frontend__core___Ast__module_state__ast_reset
#7 cli__check___check_path
#8 cli.check.run_check
```

The complete backtrace, registers, mappings, and a recoverable 48 MiB core are
retained at `build/native_probe/frontend_crash_capture/gdb.log` and
`build/native_probe/frontend_crash_capture/core` respectively.

Static disassembly of this exact ELF proves the mismatch without relying on
optimized argument recovery:

- `expr_count_set` at `0xc11f0d..0xc11f20` computes both strings with
  `rt_string_data`/`rt_string_len`, puts key pointer/length in `rdi`/`rsi`,
  value pointer/length in `rdx`/`rcx`, and calls `rt_env_set`.
- `rt_env_set` at `0x2af5a47..0x2af5a68` ignores `rdx` and `rcx`, treats
  `rdi`/`rsi` as the two arguments to libc `setenv`, places `1` in `rdx`, and
  calls it.  Therefore the correct key length `27` (`0x1b`) becomes libc's
  value pointer and `strlen(0x1b)` faults exactly as captured.

Current source is already coherent: `src/runtime/runtime.h`,
`src/runtime/runtime_native.c`, `src/runtime/simple_core/core_env.spl`, and the
MIR text-extern registry all define or emit the four-word contract.  No
frontend source change is warranted.  The smallest owner is compiler artifact
assembly/admission: it must not combine a current caller with an obsolete
runtime provider.

## Reproducer scope

The two failing focused operations were run from
`/mnt/data/worktrees/simple-mcdc-hal`, with
`SIMPLE_LIB=/mnt/data/worktrees/simple-mcdc-hal/src`:

```text
timeout 180 /mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/driver/native_mcdc_transport_spec.spl --mode=interpreter
timeout 180 /mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple check test/01_unit/compiler/driver/native_mcdc_transport_spec.spl
```

Each exited 139.  A fresh-session capture should run each operation at most
once, with core capture enabled, and must record the resolved executable
identity before execution.

Do not replace this with a Rust-seed run: seed behavior is diagnostic only and
cannot admit the pure-Simple compiler or this feature.

## Classification

The crash is an artifact-link ABI mismatch, not MCDP publication, parser data
corruption, or a text lifetime defect.  `expr_reset()` is merely the first
caller to expose it.  Changing the manifest format, its reusable buffer, or
frontend environment mirroring would hide the failure without repairing the
mixed compiler/runtime identity.

## Fresh-session capture and unblock

1. Rebuild the pure-Simple compiler and runtime capsule from one frozen source
   identity, with stub fallback disabled and no Rust-seed substitution.
2. Before promotion, inspect the produced ELF and execute a focused
   `rt_env_set("k", "v")` ABI smoke that proves the linked provider consumes
   four words and the environment observes the exact value.
3. Run the failed standalone MCDP `check` once, then its focused test once only
   if the check passes.

Unblock condition: a source/runtime-matched admitted pure-Simple compiler whose
four-word environment ABI smoke and focused standalone MCDP check pass.  Until
then, native MCDP Simple execution and its performance evidence remain
unverified.
