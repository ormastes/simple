# Native session allocator residency

## Provider correction and scope

Final-symbol inspection established that the affected P2 compiler selects the
**Rust** `rt_session_heap_end` from `simple_runtime::value::collections`, through
its hosted `libsimple_native_all.a`. Its `__rdl_alloc` branches to glibc malloc,
but glibc imports alone did not establish C runtime ownership. The original
C-owner experiments below are valid component evidence, not P2 fix evidence.

The correction applies the same coarse boundary to both owners. The Rust owner
explicitly drops its session Vec/HashSet after freeing tracked objects, then
calls `libc::malloc_trim(0)` under `cfg(all(target_os = "linux", target_env =
"gnu"))`. Its TLS borrow and registry locks have already ended. The C owner
trims after releasing its lifecycle lock. Neither path trims rejected ends or
hot module boundaries; unsupported platforms retain existing behavior.

The public-ABI fixture can also link an explicit Rust runtime archive:
`sh scripts/check/check-session-heap-reclaim.shs --runtime-archive PATH`.
It fills every array backing page and checks the actual linked trim call,
refused ends, surviving allocations and subsequent sessions. The focused Rust
unit test is
`bsm_p1_session_reclaim_preserves_unrelated_roots_and_refuses_active_scope`.
The rebuilt Rust archive fixture and focused Rust unit now pass. Final P2
disassembly and manager validation remain pending; see the evidence below.

Snapshot accounting is provider-specific: the actual old P2's Rust
`rt_heap_live_bytes` counts registered headers, with container backing storage
tracked separately by `rt_heap_aux_live_bytes`. The core-C fallback covers only
optional SPL memtrack allocations. Neither alone is total live process heap.

The Linux native BuildRunner manager exceeded its 9.5 GiB aggregate RSS guard
inside a 10 GiB container while lowering its 1,523-module closure. Its waiting coordinator retained
about 1.8 GiB of anonymous resident pages after reporting session reclamation.
That observation alone does not distinguish live objects from allocator pages.

An isolated C probe linked the actual frozen `runtime_native.c` and allocated
32,768 runtime arrays with 1,024 slots each inside a session. An unrelated runtime
array and an ordinary malloc allocation remained live across session end.
On aarch64 Linux/glibc, mallinfo2 and /proc/self/statm reported:

| Boundary | Live heap bytes | Free arena bytes | Resident pages |
| --- | ---: | ---: | ---: |
| Allocated | 270540560 | 16624 | 66575 |
| Session reclaimed | 8288 | 270548896 | 66510 |
| Explicit malloc_trim(0) | 8288 | 540576 | 467 |

The owner correctly frees objects, but libc can retain nearly the entire freed
arena. Requesting trim after successful session reclamation returns unused
pages without changing object ownership. The call occurs after releasing the
runtime lifecycle lock and is guarded by `__GLIBC__`. Other platforms keep their
existing behavior. No per-module trim or allocation-policy tuning is introduced.
A failed trim is harmless: its result is advisory and does not alter successful
session completion. Sessions are coarse compiler epochs, unlike hot module scopes.

`sh scripts/check/check-session-heap-reclaim.shs` links the real runtime and
checks unrelated live allocations, active/paused module refusal, wrong session
IDs, repeated end refusal, and a subsequent session. On glibc the linker wrapper
asserts exactly one trim request per successful session and zero on rejected
ends. mallinfo2 checks live reclamation when glibc >= 2.33 is available; RSS is
reported only by the investigative probe, never used as a brittle test assertion.
The fixture passed on Darwin (unsupported allocator path) and aarch64 Linux.

This fixes demonstrated allocator residency, not proven total manager memory.
A source-matched native manager run must still measure aggregate RSS and finish
the real build; neither the probe nor these tests establish that outcome.

## Controlled red/green runtime experiment

A second isolated experiment used the fixed source twice, removing only the
`(void)malloc_trim(0);` statement for the baseline compilation. Both binaries
linked the same probe, optimization and section-GC flags, and ran in dedicated
processes. All array backing slots are touched by `rt_array_new` initialization.
Immediately after session end (before the probe's later explicit trim):

| Variant | Live bytes | Free arena bytes | Resident pages |
| --- | ---: | ---: | ---: |
| Baseline, session trim omitted | 8288 | 270548896 | 66509 |
| Fixed, session trim enabled | 8288 | 540576 | 467 |

Thus the production session boundary releases 66,042 resident pages on this
host while preserving exactly the same live allocation total. The baseline's
later explicit trim also reaches 467 pages. This controlled red/green result
establishes the intended residency effect separately from trim-call counting.
Receipts: `/tmp/session-reclaim-probe/rss-{baseline,fixed}.log` in the isolated
Linux lane, copied to `/private/tmp/session-reclaim-probe/` on the host.

## Actual Rust owner baseline

The updated public-ABI fixture linked the frozen C-only build's
`/work/bootstrap-stage2-memory-rti-20261030/stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority/deps/libsimple_runtime.a` successfully and failed at
`trim_calls == 1` (status 134, core dumps disabled). This is the expected red
baseline: the original Rust session owner never requests trimming.

A separate dedicated process linked that same actual Rust archive and filled
8,192 arrays of 1,024 slots through public runtime calls. It preserved an
unrelated runtime array and ordinary malloc allocation:

| Boundary | Live allocator bytes | Free arena bytes | Resident pages |
| --- | ---: | ---: | ---: |
| Allocated | 67920240 | 48784 | 17387 |
| Rust session reclaimed | 235616 | 67868576 | 17386 |
| Explicit malloc_trim(0) | 235616 | 67745696 | 940 |

The explicit trim releases resident pages inside retained arenas even though
arena virtual size changes little. This establishes the same residency defect
for the actual Rust owner. The patched results below are separate executions;
they are not inferred from this baseline experiment.

## Rebuilt Rust owner validation

Combined source `b9c91bb40b93408388841210e679cfba613342a1` rebuilt the Rust
runtime with the reviewed correction. Its frozen `deps/libsimple_runtime.a`
SHA256 is `ada5dc7ee2a06ad0473584360d4bfc9869b17c3c8c5b1a5bb5d8ba05ba76a6c5`;
`libsimple_native_all.a` is
`3aa5291091fca8534304916e912f1de3da3c6f72c99205962a85eb38f4119c59`.
Both archives contain exactly one strong Rust session owner with the trim
relocation after session container drops. Before/after pins match.

The archive-linked ABI fixture passed (one executable, no failures), including
zero trim calls on refused ends and one per successful end. A separate actual
Rust-owner RSS probe measured 17,415 resident pages while allocated, 952 after
session end, and 952 after a further explicit trim. Its live allocator bytes
were 238,128 at both post-end measurements. These are separate probe values,
not the smaller ABI fixture's allocation totals.

The authored Rust unit executed exactly once: one passed, zero failed, zero
ignored, 1,451 filtered. It completed in 1m17s under a 3 GiB watchdog, with
peak RSS 1,272,108 KiB, complete observation and quiescence. Cargo reported
existing library-test warnings but no compilation or test errors. Source and
frozen archive pins remained unchanged; the target directory was isolated.

Evidence is under `/private/tmp/buildrunner-linux-lane-20261029/session-provider-audit/`:
`rust-session-fixed-b9c91/` holds ABI, RSS and provider records;
`rust-unit-b9c91-evidence/` holds the Rust unit log and watchdog receipt.
The final linked P2 provider and the actual manager's aggregate RSS still need
validation. These component passes do not establish BuildRunner Hello success.
