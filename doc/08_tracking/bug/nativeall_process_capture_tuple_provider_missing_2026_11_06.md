# Native-all lacks the unbounded process result-block provider

Canonical ID: `nativeall_process_capture_tuple_provider_missing_2026_11_06`.
Severity: P1. Status: source repair implemented; executable verification pending.

## Reproduction and source authority

Windows Phase Ladder run42208248396/job127860185705 at source
`04c3470126023edd7ef19c0e89576dff5dce812a` compiled1607 objects but failed
linking Phase1 against its real Rust `libsimple_native_all.a`. The original
linker stopped after20 errors. A link-only replay of the exact retained two
archives and three entry objects, with matching20260922 UCRT Clang/LLD hashes
and41 matching installed system/startup inputs, removed that diagnostic limit
and proved97 actual missing symbols, including `rt_process_run_tuple`.
No source was recompiled, no seed/program was executed, and no successful
Phase1 receipt was inferred from this failure.

This narrow repair is based on release
`4344ed97ed9e18ec20e8a568378f4c34afceea65`. The caller, Rust owner, call-lowering
owner, Rust allocator/tuple owners, and C memory/process-tree owners have the
same blobs as the failed source. The source is still unchanged for these
owners at later release `fd45e21b30f448e9e528b151bf3eb8179bd68574`.

## Physical ABI and ownership

The actual Simple declaration/call in
`src/lib/nogc_sync_mut/sffi/process_capture.spl` supplies three words:
`(command_ptr: i64, command_len: i64, args: [text]) -> i64`. The command is
retained for the synchronous operation and has an explicit byte extent.
The new Rust export takes `(*const u8, u64, RuntimeValue) -> *mut i64` and
delegates to the existing `rt_process_run` and `process_result_block` owners.
Arguments and text payloads remain Rust runtime values; no C private string
header, C managed array, or substitute process implementation is introduced.

The existing helper allocates24 bytes through the shared C `rt_alloc` owner,
copies two runtime payload words plus an untagged signed status, then shallow
frees only its fresh tuple. If allocation refuses, it returns null before the
copy and still releases that fresh tuple. The C tuple providers also return
fresh `rt_alloc` blocks. The only Simple consumer calls are the bounded and
unbounded capture paths; neither supplies a borrowed/static block.

The consumer previously never released this raw block. It now calls the same
allocator's `rt_free` once after copying both streams, and on the invalid-text
early return. The null path never frees. Only the three-word block is released;
managed payload ownership is not changed. `rt_free` unregisters the block and
removes its transient raw entry before normal release or quarantine, so later
scope teardown has no stale block to free again.

## Regression and qualification boundaries

- Rust owner tests exercise both real child streams and status7, empty output,
  spawn failure status-1, actual allocation registration/removal, transient
  scope teardown and payload access after raw block release. Run single-threaded.
- `test/01_unit/lib/nogc_sync_mut/process_capture_owned_result_spec.spl`
  exercises the actual consumer with null, NIL streams/raw negative status,
  invalid handles in either stream, real streams/status and real empty output.
  It requires an admitted, source-matched P2 compiled runner.
- `test/fixtures/compiler/process_capture_owned_block/main.spl` requires
  `SIMPLE_MEM_HARDEN=1` before process startup. The real allocator quarantine
  avoids address-reuse ambiguity. The fixture queries both the real allocation
  registry and raw scope table after normal/invalid-text consumption, ends its
  owned scope, then accesses copied payloads. Required stdout is exactly
  `process capture owned block OK`.

Rust/C/P1 harness or fixture results are diagnostic only. They do not qualify
the Simple SSpec runner or prove the other96 Windows link blockers are fixed.
The null-allocation branch is source-reviewed; a forced allocator-refusal
execution is not claimed. Native tests, required compiler/core/MCP gates and
admitted P2 SSpec execution are **UNRUN** until recorded evidence says otherwise.
No real Cranelift provider is removed, no core-C trap bundle is substituted,
and no broader native-all provider family is changed by this repair.

## Bounded preflight (diagnostic only)

Source-only offline locked Cargo metadata succeeded without compilation. The
private target budget is 3 GiB, log budget 32 MiB, and required free disk reserve
is 2 GiB. Heavy execution remains pending review of a private Windows Job guard
with an 8 GiB hard committed-memory limit and at most two allowed CPU cores.

SFFI host-map coverage passed as a mapping check only. The pointer map check
reported Windows path-separator baseline mismatches in unrelated symbols; a
separate owner is repairing that checker. The warning-queue prerequisite failed
its existing source inventory counts (265/399 variants; 3704/3546 migration).
Neither failure is waived or presented as native execution evidence.

Current repair cycle is 1/6: source repair and focused regression authoring.
No runtime behavior acceptance result exists yet.

First Rust runtime diagnostic execution stopped with Cargo exit101 before the
owner tests: host build scripts `quote` and `proc-macro2` could not find the
configured MSVC `lld-link`. The gnullvm target LLVM-MinGW tools were present,
but the clean environment did not include the separate host linker/SDK. No
retry occurred and no tests were selected or executed. The frozen private Job
guard reported no resource error, peak committed memory 335691776 bytes,
peak sampled RSS 193552384 bytes, and target allocation 3379200 bytes.
The cache and full command/log/receipt were preserved for command review.

The bounded host-toolchain repair preflight passed using pinned Rust, the
existing LLVM `lld-link`, and installed MSVC/UCRT/UM import libraries. Runtime
attempt2 then advanced dependency compilation but the private guard stopped it
with exit125: its fail-closed target inventory exceeded the reviewed 250 ms
scan budget. Cleanup reaped the entire Job. Peak committed memory was
667217920 bytes, peak sampled RSS 592293888 bytes, and target allocation
49528832 bytes. No owner tests executed and no automatic retry occurred.
This is repair cycle2/6; private cache and exact receipts are retained.

Attempt3 compiled the real runtime and executed all three named owner tests:
both-stream/status and empty-output/spawn-failure passed; lifecycle failed
because its oracle queried the struct registry for an `rt_alloc` raw block.
`runtime_memory.c:549` adds struct registration only for `rt_struct_alloc`;
`rt_transient_raw_words` is the correct raw-allocation query and returns three
words while live and minus one when absent. The current test and fixture also
incorrectly expect zero for absence. Production was not changed or retried
after this result. Owner lifecycle acceptance remains FAIL pending correction.
The repaired private guard completed without resource errors; its maximum
target scan was 767 ms under its two-second soft budget. Cycle3/6 recorded.

## Final focused Rust owner result

Attempt4 corrected only the test/fixture oracle, selected only the full named
lifecycle test with `--exact --test-threads=1`, and passed exactly one test.
The two passing attempt3 cases were preserved and never rerun. All three new
Rust owner cases therefore have diagnostic PASS evidence: real streams/status,
empty output/spawn failure, and raw registry removal/scope exit/payload survival.
The actual raw query proves three live words and minus one after free.
Production wrapper and consumer bodies did not change between attempts3/4.

The frozen private guard reported child exit0, no resource error, peak committed
memory1274658816 bytes, peak sampled RSS1172905984 bytes, target279130112 bytes,
maximum target scan619 ms, and minimum free disk10879053824 bytes. The scan is
a synchronous soft sample; no hard filesystem quota or exact RSS sampling
interval is claimed. Exact command/environment/source hashes and full receipts
are retained under the worktree's Git evidence directory. Repair cycle4/6.

The corrected standalone Simple fixture is authored and **UNRUN**. Simple
consumer SSpec, admitted P2, native-all provider composition and broader core
checks remain **UNRUN**; Rust owner results do not establish those admissions.
