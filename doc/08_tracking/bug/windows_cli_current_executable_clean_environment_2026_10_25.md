# Independent bug draft: Windows executable lookup with OS absent

Status: reproduced by native baseline; fixed standalone Windows regression PASS.
This is a new executable-identity cause, not permission to retry the frozen
preclosed receiver, whose six-cycle budget remains exhausted.

## Retained observation

The immutable core-C diagnostic SHA256
3cdccde832e0ea57228d8ee0e3864a793d17dec20a1b7fa360bea9712124b0ae
exited 1/raw0x1, quiescent, before receiver assertions. It printed
`actual diagnostic producer digest unavailable` after its real temporary Git
project and SCV setup. The fixture applies file_hash_sha256 to
cli_current_exe_path and requires 64 hex characters. The actual returned path
was not logged. Do not present any derived path spelling as observed output.
Evidence: C:/dev/simple-preclosed-owner-negative-lean-storage-20261025/evidence-attempt3/final-terminal-result.sdn.

## Exact source chain in the executing diagnostic source60304

- Reviewed actual run-attempt3b-argv.sdn supplies env -i with no OS variable.
- run-process-group-bounded-log-windows.py:60-76 consumes that prefix into an
  initially empty environment and passes that explicit block to CreateProcess.
- app/io/cli_ops.spl:52-57 decides Windows only from env_get("OS"); nil means
  false. It therefore classifies this real Windows invocation as non-Windows.
- cli_ops:257-262 enters the Unix /proc/self/exe branch before reading argv.
  It accepts any nonempty canonicalization result unequal to the literal,
  without checking existence or asking the Windows kernel image owner.
- cli_ops:161-170 _cli_resolve_symlink calls imported path_absolute.
  runtime_native.c:13531-13544 uses Windows _fullpath. This lexical Windows
  operation can produce an absolute result for a nonexistent /proc/self/exe.
- nogc_sync_mut/io/file_ops.spl:292-294 forwards host_path_native(path) to the
  genuine rt_file_hash_sha256 owner (runtime_native.c:16589-16602), which calls
  rt_sha256_file_raw_v1:16540. Windows opens the wide path with _wfopen(...rb).
  A nonexistent lexical path returns nil; no 64-character digest is available.

The actual link command selects generated core_c_runtime/simple_runtime.lib.
The retained unresolved-symbol preview contains 13 time/timestamp names, not
rt_file_hash_sha256 or sys_get_args. The native hash owner exists; provider
absence is not the source explanation. Exact old returned bytes, and the
precise branch observed inside the binary, remain uninstrumented.

## Small pure-Simple correction (authored, native UNRUN)

At the start of _cli_current_exe_path, use host_os()==windows and call the
already-existing cli_kernel_executable_path. Fail closed if its kernel query
fails rather than selecting a Unix lexical substitute. Preserve Unix handling.
Do not remove authentication checks, substitute a nominal executable identity,
or weaken the fixture's producer digest requirement.

Call graph: cli_kernel_executable_path:234-248 -> host_os (runtime platform
owner, independent of OS/OSTYPE) -> windows_image_path ->
windows_image_path_with_capacity:40-54 -> GetProcessHeap/HeapAlloc,
GetModuleFileNameW(0,...), bounded UTF16 copy/checked decode, HeapFree.
Then cli_kernel_executable_path checks file_exists and calls path_absolute.
None of those calls uses cli_current_exe_path, argv, SIMPLE_BINARY, PID-helper
processes, or a recursive call back into the executable-identity owner.

## Independent regression design and actual execution

A new standalone fixture imports only existing app.io.cli_ops current/kernel
identity helpers, the normal argv facade and nogc_sync_mut.io.file_ops hash.
It imports no CompilerDriver, parser, HIR, MIR, source loader, or SCV receiver.
After native compilation, the collector pins the ACTUAL executable SHA256 and
passes it as an ordinary fixture argument; do not hardcode a producer digest.
The fixture obtains both current and kernel executable paths, emits bounded
actual diagnostic values on failure, and asserts real nonempty kernel/current
paths, equality to the kernel result, existing image bytes, and SHA256 equality
to the externally pinned compiled executable. Never accept an unverified path.

Run the same immutable fixture in separate fresh processes for OS absent,
OS=Linux with bogus SIMPLE_BINARY, and normal OS=Windows_NT. Separate processes
prevent the process-lifetime current-path cache from masking the first lookup.
Each case also repeats the successful identity call to exercise the cache.
Bind actual target/runtime provider and normal source/producer/tool identities,
use a private normal-key cache, 24 jobs and the unchanged 5,859,375 KiB guard.
No compiler/Rust-seed rebuild, relaxed guard, fake OS capability, or rerun of
the old preclosed fixture is part of this independent proposal. A bootstrap-only
SPL diagnostic would need explicit owner approval and truthful actual provider
labeling; it would not qualify the parent compiler or descendants.

## Authored implementation and execution status

The isolated release39af patch now uses the existing runtime-backed `host_os()`
for `_cli_is_windows_platform`, and Windows `_cli_current_exe_path` returns the
existing kernel-image owner before argv, environment overrides or Unix lexical
canonicalization. Public signatures and configured import families are unchanged.
`test/fixtures/bootstrap/windows_current_executable/main.spl` contains nine real
assertions with an externally supplied actual executable digest. Separate fresh
OS-absent/misleading/normal profiles and an identical-byte Unicode/spaces copy
passed native execution as recorded below. Fable plan/code review artifacts
are separate source review evidence, never native qualification. The previous
preclosed receiver remains frozen after its final failed setup and six cycles.

Actual Fable 5.1 high plan and code reviews completed with conditional approval.
The get_args re-export is present. The fixture calls current lookup first and
checks paths before hashing; the kernel helper now rechecks resolved existence.
Existing test_runner_client.invoking_binary, test_runner_single.find_simple_binary
and light_daemon contain their own fallback policies, which are unchanged.
No global downstream fail-closed guarantee is claimed.


## Actual native baseline and fixed evidence

The independent baseline used the exact same nine-assert fixture with old
release39af CLI source and the immutable 5a6 seed solely to compile a bootstrap
SPL diagnostic. Native build succeeded: 59 fresh modules, zero failures,
quiescent cleanup, 7.465 seconds collector wall time. The ACTUAL linked provider
was generated core-C `simple_runtime.lib`, not the nominal Rust058 directory.

With OS absent, the baseline printed its real kernel image path and the wrong
current image `C:\proc\self\exe`, then the expected ordinal-4 current-versus-kernel
failure. The native assertion owner `runtime_contracts.c:22-29` printed the exact
Assertion violation and called `abort()`: actual native status was `0xC0000409`,
collector reason `child-native-status`, wrapper exit 125, quiescent cleanup.
This deliberate contract-abort reproduction was accepted on its actual owner
and ordinal. Preserve `ordinary_semantic_exit=false` and `owner_harness_pass=false`:
the stricter ordinary-exit harness did NOT pass and its result was not rewritten.
The baseline was not rerun. This observation is distinct from the old preclosed
receiver's unlogged path and does not reopen its exhausted six-cycle budget.

The fixed build used a private copy of the completed baseline cache, normal
keys only: 41 cache hits, 18 fresh modules, zero failures, native exit 0,
quiescent cleanup. Module compilation took 1.0 second, collector wall 7.888
seconds, peak RSS 1,462,080 KiB. Its actual target provider was core-C too.
Actual fixed executable SHA256:
`e7390e6e324220589c92ce410b4e60e20067fe3731dac07c5c8781f310bdd92f`.
Each run independently required that digest as an explicit argument; the runner
verified the original and Unicode copy hashes before AND after execution.

| Fresh process profile | Actual assertions | Native exit | Quiescent | Collector wall seconds | Peak RSS KiB |
| --- | ---: | ---: | --- | ---: | ---: |
| OS absent | 9 | 0 | yes | 0.308341 | 40,312 |
| OS=Linux and bogus SIMPLE_BINARY | 9 | 0 | yes | 0.311773 | 28,840 |
| OS=Windows_NT | 9 | 0 | yes | 0.324952 | 29,208 |
| OS absent, identical binary in Unicode/spaces path | 9 | 0 | yes | 0.306344 | 40,200 |

Each stdout was exactly `windows-current-executable assertions=9` plus LF.
These 36 actual assertions are focused app/io evidence, not full CLI, compiler,
bootstrap descendant, or MCP/LSP qualification. Timing includes collector/startup
cost and is not a microbenchmark of the image API. Native source/verification
cycle 1 converged; no passing profile was repeated.

Evidence root: `C:/dev/simple-windows-cli-image-identity-storage-20261025`.
`evidence/baseline/baseline-observed-reproduction.sdn` binds the failed assertion
owner and raw receipts; `evidence/fixed/*-timing.sdn` binds actual receipt/RSS
hashes. Inputs, source commits, actual argv and tool/provider evidence are retained.

## Applicable check scope

The only production path changed is `src/app/io/cli_ops.spl`. No compiler, lib,
runtime, MCP/LSP implementation, package, npm or publication path changed. The
conditional mandatory compiler/lib checks, MCP native package smokes and npm
publication smoke therefore are not triggered by this scoped app/io repair.
The focused real native fixture, environment-owner guards, spec-layout check,
whitespace review and exact PR review are applicable. No unavailable broad check
is silently converted into PASS. The unrelated preclosed receiver's full CLI
and negative gates remain incomplete on its separate draft PR.
