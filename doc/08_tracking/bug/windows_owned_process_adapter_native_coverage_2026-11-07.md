# Windows owned-process adapter native coverage

Bug: `trace_owned_process_windows_adapter_no_c_unit_test_2026-11-06`.
Status: native boundary tests passed; independent source review approved;
self-hosted Simple qualification pending.

The prior generic adapter selfchecks compile a no-op main on Windows. The
existing Windows core selfchecks use RT_PROCESS_OWNED_CORE_ONLY and omit the
SplArray/opaque-handle adapter. This change adds that missing Windows-only
test boundary. Production runtime source and headers remain unchanged.

## Actual native evidence

Isolated checkout: `D:/dev/simple-windows-owned-adapter-test-20261107`.
Source baseline: `d1b8b8e164e9330cc9625607e1903538ddc4ca14`.
Pinned clang-cl/lld-link 23.1.1, MSVC 14.44.35207 and SDK 10.0.26100.0
compiled and linked the test. Compile, link and execution exited zero.
Actual output: `PASS Windows opaque process adapter checks=182`.

Evidence directory: `build/windows-adapter-attempt1/`, including exact argv,
stdout/stderr, exit status files, executable and `qualification.sdn`.
The receipt binds both tools, the executable and eight source/header hashes.
The initial receipt had a PowerShell array-concatenation formatting error;
only serialization was corrected using the retained logs and matching
source/tool/executable hashes. Original serialization and executed-harness
hash remain retained. The passing native test was **not rerun**.

The test includes the actual runtime_process_owned.c provider and requires
RT_OWNED_WIN32_V3_ADAPTER; CORE_ONLY is a compile error. Its small value host
provides real SplArray layout, text storage and allocation helpers, without
replacing process, token, handle, cancellation or capture implementation.
Non-Windows execution returns 77; NDEBUG is rejected.

## Assertions

- Actual child argv preserves a spaced argument, an empty argument and
  embedded quote/backslash boundaries; stdout and stderr remain separate,
  and the child's nonzero exit 7 reaches the result receipt.
- Start, poll and result arrays retain their 4/17/15-word schemas and versions;
  byte-array lengths agree with delivered counts.
- Observation retains the opaque lease; collect consumes exactly that lease;
  stale result and double release cannot regain authority.
- Embedded-NUL argv is rejected before a child or adapter lease is created.
- A 50ms deadline terminates and reaps the owned sleeping child.
- Bounded stdout/stderr retain truncation and seen-byte evidence.
- Early collect leaves a live lease intact; an old handle cannot cancel a
  reused slot; the current owner can cancel and collect its own child.

The harness bounds compilation to 90s, linking to 30s and execution to 30s,
uses a fresh private output directory, and checks positive assertion output
and unchanged source hashes. The executable path itself contains spaces.
No Cargo or Rust seed is used by this native test. This result does not
qualify the Simple value representation, process facade, compiler or test
runner. Keep the canonical bug in `fix-implemented-verification-pending`
until an admitted, source-matched Simple facade test satisfies the remaining
consumer gate. No release qualification is claimed.
