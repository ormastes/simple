# Windows SOSIX process capture after environment admission

The rejected Stage2 candidate `c72ab722ea1ae171079f1b577302fabf041f10b616c791b6c2c72fa618999240`
first aborted at the SOSIX environment gate. After that separate repair,
`driver_aot_native_output.spl` calls `sosix_run` for the compiler version probe
and actual linker. The old process route also rejected Windows, and its bare
resolver depended on `/usr/bin/which`. Directory, spawn and stdio admission
are separate operations and remain unsupported by this SOSIX Windows facade.

## Repair and contract

`rt_process_run_bounded_bytes(cmd, args, timeout_ms, max_output_bytes)` has five
physical ABI arguments: command pointer/length, tagged argument array, timeout,
cap. Its registered tuple contains two byte arrays and an integer status.
It preserves the exact prefix of each stream, up to the selected cap, including
NUL and malformed UTF-8. Zero cap retains nothing while still draining pipes.
No truncation marker, timeout marker or fabricated spawn diagnostic enters the
captured bytes. Normal status is preserved; timeout/execution failure is -1.
The new operation limits output to 16 MiB per stream and rejects negative bounds.

Simple's `sosix_decode_process_bytes` performs strict UTF-8 decoding and returns
a typed `TextIoError.Codec` on malformed bytes, including an incomplete scalar
at a byte-cap boundary. The Windows checked process route uses that decoder.
Its resolver uses the existing host PATH/PATHEXT and file-existence boundaries,
recognizing forward slash, backslash and drive paths without POSIX `which`.
Existing text process APIs retain their previous semantics.

Rust owns the new ABI strongly, including native-all. C supplies genuine weak
fallbacks (private MSVC `core_c_*` plus alternatename). Windows C reuses the
bounded pipe/JobObject engine with strict UTF-8 command-line conversion and
`CreateProcessW`/a Unicode environment block. Rust retains its bounded engine,
adds exact-prefix reader mode, and assigns a suspended child to a kill-on-close
Job before resuming it. Normal parent exit also terminates descendants before
waiting for pipe completion. One finite ToolHelp snapshot finds the suspended
child's retained PID; it is not a retrying process scan. The pinned Rust rejects
`ChildExt::main_thread_handle` with E0658 unless a new unstable feature is enabled,
so the existing Windows crate ToolHelp feature is used instead.

A genuine POSIX C weak counterpart reuses the existing fork/poll capture engine
in prefix mode, preventing an undefined ABI reference for POSIX C-only consumers.
Reserved trailing NUL storage is maintained for legacy exec-error classification;
the terminator is excluded from the returned byte length, even at cap zero.

## Actual focused evidence

Private source/evidence: `D:/dev/simple-gpu-owner-landing-20261021`,
`build/windows-process-bytes/`. The source incorporates the reviewed environment
repair before process tests. All build/cache writes were private; the idle Cargo
target was explicitly handed off by its prior owner and used with two jobs.

- `c-native.sh`: C-only native ABI witness, 25 checks, zero failures. Includes
  Unicode executable path/quoted arguments, both raw malformed/NUL streams,
  nonzero status, exact cap33/cap0, timeout cap0, timed-out grandchild and normal
  parent exit with inherited-pipe grandchild; both grandchildren confirmed dead.
- `rust.sh` / `qualified-runtime.sh`: actual aggregate-feature Rust integration
  test passed in 2.11 seconds; same boundaries plus unchanged process handle and
  thread counts after capture. Initial test-only import errors were corrected
  before the first execution; the production runtime compiled successfully.
- `raw-mixed.sh`: new native-all plus fresh core-C supplement, 25 native checks,
  zero failures. No public values cross a private C string registry.
- `codec-mixed.sh`: 52 modules compiled, zero failed; executable prints
  `PASS native Simple strict byte decoder and Windows PATH resolver`. It checks
  genuine Unicode capture, typed Codec rejection of malformed captured bytes,
  and a Unicode PATH directory resolving the actual PE child executable.
- `prelaunch.sh`: missing/empty command failures return no invented capture;
  zero failures. This covers the final C failure-path refinement separately.
- `posix.sh`: WSL Ubuntu24.04 actual production C values and capture engine,
  nine checks, zero failures; no stub runtime or duplicate-symbol allowances.
- `posix-exit127-asan.sh`: focused AddressSanitizer execution of exit127 with
  cap0/cap3 stderr, zero failures and no sanitizer report. This verifies the
  review-discovered reserved-terminator fix without repeating the old matrix.

The mixed runtime uses new unstripped native-all SHA256
`fcda442b66a8d1f72d0cd6ae65631afea082f60799ab9e829fe06d068f4e1cad`
and unchanged frozen bootstrap-only producer
`53c3b6783a25170093e74c4c96be316289d34b8a93c9e13795d2610f31cdcea0`.
`mixed-runtime/diagnostic-identities.txt` records the distinct components; no
frozen archive, cache receipt or producer identity was rebound. LLVM strip did
not support an archive member; the exact unstripped archive was copied afresh.
POSIX-only source corrections followed archive completion and were tested on WSL.

## Qualification limits and follow-ups

The old producer predates this runtime name's text ABI metadata. Native witnesses
therefore call zero-argument C entrypoints that invoke the exact five-argument
ABI. The real Simple decoder/resolver execute, but the production text-argument
wrapper is **unqualified until a fresh registered canonical producer executes it**.
Both Rust codegen argument tables, RuntimeFuncSpec, ELF lookup and the Simple
text extern ABI table are updated for that fresh producer. The authored full
facade fixture is `test/fixtures/runtime/windows_process_bytes/main.spl`.
The pending criterion is to compile and execute that fixture once with a fresh
qualified Phase2/Phase3 self-hosted producer: forward-slash and backslash Unicode
PE paths, actual bare-name invocation, strict malformed-output rejection. The
retained runner is `build/windows-process-bytes/full-facade-qualified.sh
<qualified-producer.exe> <matching-runtime-directory> <Unicode-child.exe>`;
its required child is the real compiled `child.c` fixture. This row has not run.

Qualification covers PE executables, not Windows batch parity. PATHEXT lookup
can find BAT/CMD files, but C CreateProcessW does not automatically interpret
them; adding a safe batch host route is a separate concrete follow-up. Rust's raw
entry additionally enforces 1 MiB command, 65536 arguments and 16 MiB argument
bytes; direct C raw invalid-input behavior is not claimed identical. The Simple
checked boundary admits its text/argument sizes before invoking either provider.
No full compiler bootstrap, product suite, MCP console/directory support or
cross-host qualification is claimed by these focused rows.
