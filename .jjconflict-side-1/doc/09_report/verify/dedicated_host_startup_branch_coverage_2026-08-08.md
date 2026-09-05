# Dedicated Host Startup Branch Evidence — 2026-08-08

This is a decision-path ledger, not compiler-instrumented branch coverage. No
percentage is claimed because the current Simple test runner did not emit
line/branch counters for these modules.

## Executed evidence

| Area | Exercised decisions | Status |
|---|---|---|
| argv parsing | normalized argv0; separate and inline values; flag; default; unknown argument ignored; duplicate rejected; required missing rejected | PASS |
| preload | required success; required failure blocks; optional failure continues; maximum bytes blocks; unsupported mode blocks | PASS |
| mmap validation | private file and anonymous/private accepted; ambiguous sharing, unaligned offset, zero length, unknown flag, and unknown protection rejected | PASS |
| mapping lifetime | owned successful versus failed/non-owned release admission | PASS (pure contract) |
| POSIX provider | invalid map rejected before ABI; real existing file mmap-preload returns exact byte/page metadata | PASS (interpreter-supported paths) |
| POSIX platform variation | Linux bit retained; Darwin/FreeBSD and Solaris-family anonymous-map bits translated; file-map flags unchanged | PASS (pure provider policy) |
| SimpleOS provider | capability identity; anonymous/private admission; shared/file-backed rejection | PASS (pure provider policy) |
| unsupported modes | SimpleOS shared/file map and startup writable-map reject without semantic fallback | PASS |

Commands executed once after the final change:

```text
SIMPLE_LIB=src bin/simple test test/01_unit/app/startup/dedicated_host_startup_spec.spl --mode=interpreter
PASS: 9 examples, 0 failures

SIMPLE_LIB=src bin/simple test test/01_unit/app/startup/dedicated_host_provider_contract_spec.spl --mode=interpreter
PASS: 6 examples, 0 failures

SIMPLE_LIB=src bin/simple test test/02_integration/app/startup_argparse_mmap_perf_spec.spl --mode=interpreter
PASS: 2 examples, 0 failures; test-runner duration 578 ms

SIMPLE_LIB=src bin/simple test test/01_unit/app/startup/dedicated_host_posix_flags_spec.spl --mode=interpreter
PASS: 2 examples, 0 failures
```

The controlling `bin/simple` emitted the repository warning that it is a
Rust-built bootstrap seed. Therefore these results are not evidence of a
pure-Simple controlling compiler.

## Required environment evidence not yet executed

- Native POSIX anonymous `mmap -> mprotect -> munmap`; interpreter mode reports
  `unknown extern function: rt_mmap_raw`, so this was not converted into a fake
  pass.
- SimpleOS QEMU anonymous map/protect/unmap and VFS-backed preload.
- Generated native-entry and both SimpleOS crt0 variants calling manifest
  startup admission before `main`.
- In-guest Clang compile/link/run of hello-world using the recovered interface.

These remain bootstrap/environment gates. Source presence or pure policy tests
must not promote them to PASS.
