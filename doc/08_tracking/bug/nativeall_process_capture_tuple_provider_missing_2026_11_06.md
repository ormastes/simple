# Native-all lacks the unbounded process result-block provider

Canonical ID: `nativeall_process_capture_tuple_provider_missing_2026_11_06`.
Severity: P1. Status: source repair implemented; awaiting-verification;
caller diagnostic FAIL; six-cycle cap reached. The bug is not marked fixed.

## Source-only landing follow-up (2026-11-07)

The user explicitly reassigned this lane to root and requested PR7337 landing.
The original head `26c80e995b1c49f03262fa7f1a712f8431790603` and all evidence
below remain historical pins. The two source commits were rebased in an
isolated Linux worktree onto release
`a6dca22ee32da27ff9e45a67ba86ae3ef587074e`, preserving newer release changes.
Final source integration rebased that reviewed candidate onto release
`8731af00a0fc9b264e5e38ca4034e27f6b04a69c` and resealed only the owned bug rows.
The one stale `rt_process_run_tuple c-only` parity-baseline row was removed
alongside its new Rust export. No capture semantics were changed beyond the
original export and consumer block release.

Astra and Sol reviewed the physical ABI, fresh-block ownership, shallow tuple
release, and both consumer cleanup paths; no introduced P0/P1 source defect
was identified. This is source review, not runtime admission. The original
raw-only fixture's registry expectation is invalid for canonical C MEMORY_OWNER
composition, which requires array-scope activation. Whether this explains the
retained exit14 remains conditional on its unknown linked-runtime identity.

The separate canonical-scope diagnostic in PR7547 preserves the old fixture,
uses the established transient wrappers, reports actual raw-word observations,
and requires independently verified runtime provenance. It adds no conflicting
SFFI signatures against its exact parent but does add one disclosed unsigned
test observer; aggregate SFFI inventory remains FAIL. Its native execution is
UNRUN. Neither PR may convert original FAIL14 to PASS, close qualification,
reset the six-cycle ledger, or substitute Linux evidence for Windows native-all.

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

## Focused owner results

Three real Rust runtime owner cases have diagnostic PASS evidence. Attempt3
passed both streams/raw status7 and empty-output/spawn-failure status-1.
Attempt4 corrected only the lifecycle oracle, selected that exact named case
with `--exact --test-threads=1`, and passed one test; the two prior passing
cases were not rerun. This proves the Rust raw block has three registered
words, `rt_free` removes it (query returns minus one), owned scope exit succeeds,
and payload strings survive raw block release. Default `cpu-simd` remained
enabled on the pinned Windows gnullvm runtime-only build. This does not test
the native-all aggregate provider composition or admit a Simple compiler.

## Final actual caller diagnostic

Final attempt6 used published immutable source
`2a484914099f98418c5e48d0ae14afcb967d213d` and the already qualified pure-Simple
Linux P1 producer. SDK/Hello and passing Rust tests were reused, never rerun.
The native build and link passed: 51 modules compiled, 47 rebuilt, zero reused.
The actual `test/fixtures/compiler/process_capture_owned_block/main.spl`
executable ran with `SIMPLE_MEM_HARDEN=1` only for fixture execution and
**FAILED exit14**, with empty stdout and stderr. Required golden stdout
`process capture owned block OK` was not produced.

Exit14 means the raw-word count sampled before `process_capture_result` was
not three. The actual value was not printed. The fixture checks that saved
observation after its consumer calls and scope teardown; this does not prove
execution stopped before the consumer. No cause is attributed to production
freeing, compiler lowering or a runtime provider without further evidence.
The linked target runtime identity remains **UNKNOWN**.

The same bounded job recorded cgroup peak memory8321236992 bytes, host minimum
free disk7884750848 bytes and maximum explicit logs470841 bytes. Its final
inspect was saved before removal. Verified owned container metadata removal
used `docker rm --force <exact-ID>` without `-v`; exit0 and a successful daemon
container listing proved the exact ID absent. Source, named-volume cache,
outputs and bind-mounted evidence were preserved.

## Bounded attempt ledger and stop

| Attempt | Result |
| --- | --- |
| 1 | Host build scripts blocked by missing configured MSVC `lld-link`; no tests. |
| 2 | Host linker repaired; private target scan exceeded250ms budget; no tests. |
| 3 | Real runtime ran three cases: two PASS, lifecycle FAIL from wrong struct-registry test oracle. |
| 4 | Correct raw-registry lifecycle oracle passed exactly one case; previous PASS results preserved. |
| 5 | Docker lowercase absence diagnostic safely refused before container creation; no workload. |
| 6 | Case-only compatibility repair; actual caller build/link PASS, execution FAIL14. |

**STOP:6/6 exhausted.** No seventh attempt, source/test/monitor repair or passing
acceptance rerun occurred. The standalone fixture result is FAIL, not UNRUN.
The consumer SSpec, admitted source-matched P2, native-all composition and
broader compiler/core/MCP gates remain **UNRUN**. A forced allocator-refusal
execution is not claimed. No real Cranelift provider was removed and no core-C
trap bundle substituted. This lane does not close the remaining Windows link
closure or the canonical bug.

## Exact retained evidence pins

Evidence is retained under
`C:/dev/simple/.git/worktrees/nativeall-process-capture-d88f/evidence/`.
The actual caller evidence directory retains its prepared `attempt5` pathname;
`attempt6-launch.sdn` is the authoritative logical cycle6 record. Attempt5
artifacts were preserved byte-identically with a hash manifest before reuse.

| Artifact | SHA256 |
| --- | --- |
| Qualified pure-Simple Linux P1 producer | `e05b9162248105144b99ae85b1a88431e0983bcf0ac0e9a63ebc1307efe0d6bb` |
| Immutable fixture blob | `a137e1db8083af56aabb50ec4d8f41f4ab53c344c781527c6e712432d9fdc443` |
| Actual consumer source | `3b94ab361332d12e8e126301aa0c64761cfb67a5511bfdf1c14c65bd7be4138f` |
| Built caller executable | `8bd262180bb590dde0e8ba0dd104aafcc3b5749d2d4b1bd1b8754c91b6d614a7` |
| `runtime-owner-attempt3.receipt.env` | `8ff6893d4d3f38ed92a6bc5f38109b972b1795036a5c5d513d4f5ea522912a48` |
| `runtime-owner-attempt4.receipt.env` | `6504967cf9b630bb0be078ba7625848af1c4ba7d58a081ef1d7dea2afb078206` |
| `linux-process-capture-2a484-attempt5/receipt.sdn` | `125dfc56563e99e3d332a59664754696b341c46b4c5cfd86420304204b78cfb4` |
| `linux-process-capture-2a484-attempt5/host-container.receipt.env` | `0d3a471d60afc095e0c852cf8de9a85a1323d33682536a2fdb0c4509bfdd0070` |
| `linux-process-capture-2a484-attempt5/host-monitor.receipt.sdn` | `4c259de85702fe1a8630cbc4cd528ef34ffffd362e4b684666a424f66ca3cc5f` |
| `linux-process-capture-2a484-attempt5/container-removal-proof.sdn` | `873410c2958b3cde980386fac9599153b71cb8d1720a4656362095a139f04722` |
