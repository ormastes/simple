# Isolated-thread raw worker argument heuristic is test-order dependent

Status: fix-implemented-verification-pending (P0 — owner decision 2026-11-06); see "Explicit worker-closure kind" below
Status re-verified 2026-08-17 by source inspection (triage shard 02).
2026-08-12.

`native_callable()` infers `raw_worker_args` from closure-record shape/address.
Under the broad Rust test filter `isolated_thread`, the existing scalar tests
`test_isolated_thread_spawn_with_args_and_join` and its direct-function variant
returned 5 and 36 instead of 42. Their exact behavior depends on whether tagged
integer arguments are decoded by `native_worker_arg()`.

Required correction: make worker argument ABI an explicit property of the
callable record, not an address/shape heuristic, and add deterministic tagged
and raw argument fixtures. This is separate from the heap-input gate: the five
new exact rejection/channel tests pass.

Cross-runtime companion gap: `src/runtime/runtime_thread.c` passes two worker
arguments raw and lacks the Rust runtime's registered synchronized-handle
classification. It must fail closed or consume an equivalent typed transfer
envelope before claiming isolated-thread parity.

## Triage 2026-09-13

Both halves are out of pure-Simple scope: `native_callable()`'s
argument heuristic lives in the Rust seed test/runtime harness, and
`src/runtime/runtime_thread.c` is fenced C runtime. Requires a Rust
seed rebuild (worker-ABI as an explicit callable-record property) to
fix, not reachable from a .spl/.shs change. Leaving OPEN, no attempt.


## Re-scope 2026-11-05 (MIR P2 family H, Opus root-cause)

**Not a concurrency race.** The only shared state on the spawn path is
`NEXT_THREAD_ID` (atomic `fetch_add`); classification is a pure function of
the closure word. Arithmetic of the original symptom: tagged 10 and 32 are
`80`/`256`; decoded raw and re-read with `as_int` they give `10>>3 + 32>>3 = 5`.
So the worker ABI was flipped to "raw" for a *real heap record address*.

**Original flake: fixed by `b6dbcaf484f` (2026-10-20).** The old x86_64-only
47-bit ceiling read aarch64 PIE/heap addresses (> 2^47) as int-tagged words;
whether a test's `Box` landed above 2^47 depended on allocator state, hence
test-order dependence. The ceiling is now per-arch (48-bit + TBI on aarch64).

**Evidence (Windows x86_64, `cargo test --lib isolated_thread`, 3 runs):**
11/11 pass each run; full `executor` filter 23/23. New specs in
`src/compiler_rust/runtime/src/executor_tests.rs`:
- `test_isolated_thread_worker_args_stress_concurrent_spawners` — 16 spawner
  threads x 32 spawns, closure + direct records interleaved, exact 42.
- `test_isolated_thread_heap_record_word_is_never_raw_abi` — 4096 live
  records, none classified as the raw ABI.
Sibling paths audited: `rt_thread_spawn_limited{,_with_args}` share
`native_callable`/`native_worker_arg` and are covered by the same rule.

**Residual defect (still OPEN): the encoding is ambiguous below 2^44.**
Repro: a record at a Windows heap address (~2^40) encoded `addr << 3` stays
under `NATIVE_USER_VA_MAX`, so `native_word_exceeds_user_va` is false, the
word is used as the record address unchanged, and the raw ABI is not
selected. A fixture asserting the tagged form failed at
`assert!(native_word_exceeds_user_va(word))` on this host. Also the C twin
diverges: `runtime_thread.c` sets `raw_worker_args = 0` for single-arg and
`= 1` for `_with_args` regardless of the word.

**Next step:** make the worker ABI explicit in the callable record (e.g. a
second marker word `NATIVE_RAW_ARGS_RECORD_MARKER` emitted by LLVM/Cranelift
codegen for natively compiled lambdas), consumed identically by Rust
`native_callable` and C `rt_native_closure_payload`; then drop the VA-ceiling
inference and add the tagged-word fixture back as a passing test.

## Owner decision 2026-11-06: stays P0

Owner decision (2026-11-06): this bug stays **P0** (bug_db row raised from P2
to P0). Recorded at the owner's direction; not a triage reassessment.

## Windows-heap wrong-guess: root cause + Rust seed fix (2026-11-06, Opus)

**Root cause.** Below the user-VA ceiling an 8-aligned closure word is
ambiguous: it is either a record address (RuntimeValue worker ABI) or the
int-tagged `addr << 3` of one (raw worker ABI). On Windows the heap sits near
2^40, so `addr << 3` (~2^43) stays under the 2^47 ceiling;
`native_callable` took it as the record address and dereferenced it
(`STATUS_ACCESS_VIOLATION`, or a wrong ABI when the shifted address happened
to be mapped). Compounding it, the Windows `native_address_is_code` was a
constant `false`, so no structural validation was possible there.

**Fix (`src/compiler_rust/runtime/src/executor.rs`).** Lockless and pure: no
shared state, only `VirtualQuery` (fault-free, takes no lock of ours).
- Windows `native_address_is_code` = committed + `PAGE_EXECUTE*` region.
- `native_words_readable` (Windows) probes committed, readable, non-guard
  pages; returns `None` on hosts without a fault-free probe.
- `native_resolve_ambiguous_word` validates BOTH decodings (code address, or
  aligned readable two-word record whose entry is code). Exactly one valid
  decides the form; neither or both fails closed (spawn returns 0, never a
  guess, never a dereference). Above the ceiling the old unambiguous rule holds.

**TDD evidence (Windows x86_64, clang-cl, own target dir).** Red on the old
executor: all three new fixtures died with `0xc0000005`. Green: `isolated_thread`
filter 15/15 x3 runs, `executor` 27/27, `thread` 30/30. New specs in
`executor_tests.rs`: `..._tagged_word_below_va_ceiling_selects_raw_abi`,
`..._classifier_decodes_both_word_forms` (prevention: raw/tagged/direct),
`..._unmapped_word_fails_closed`, and the stress spec
`..._tagged_and_raw_words_stress_concurrent_spawners` (16 x 32, interleaved).

**Still open (why the bug stays open):**
- Non-Windows hosts have no fault-free readability probe here, so a low
  (non-PIE `brk`, < 2^44) Unix heap keeps the VA-ceiling rule alone.
- C twin `src/runtime/runtime_thread.c` still sets `raw_worker_args` by entry
  point, not by word; parity not claimed.
- The durable end state remains an explicit ABI marker in the callable record
  emitted by codegen, consumed by both runtimes.

## Explicit worker-closure kind: heuristic removed (2026-11-06, Opus)

Status: **fix-implemented-verification-pending**. Seed and C runtime changed.
Board and Linux runs are pending.

**Root cause, final.** One entry point took two encodings of the closure word
and had no tag to tell them apart. Runtime and test callers passed a machine
address; generated Simple code passed a tagged RuntimeValue (`addr << 3`, or
`addr | 1`). Every classifier (VA ceiling, then the #7112 dual-validation
probe) guessed from the value. A word that is valid under both decodings
cannot be decided from its value. Fixture: committed records at
A = `0x10030000` and A << 3 = `0x80180000`. Before this change the #7112
resolver rejected that word (spawn returned 0).

**Design.** The spawner states the kind; the runtime never infers it.
Lockless: pure functions with no shared state; the only probe is fault-free
`VirtualQuery`, which only rejects unreadable records.
- `RT_WORKER_CLOSURE_ADDRESS = 1`: the word is a machine address of a code
  entry or a closure record. Worker args pass unchanged. A word above user VA
  is rejected.
- `RT_WORKER_CLOSURE_VALUE = 2`: the word is a tagged Simple value, decoded by
  its own tag. `TAG_INT` (`addr << 3`) means a raw native record and raw i64
  args. `TAG_HEAP` (`addr | 1`) means a heap record and RuntimeValue args.
  Every other tag is rejected.
- Unknown kinds are rejected (spawn returns 0).
- New twins `rt_thread_spawn_isolated_kind(kind, closure, data)` and
  `rt_thread_spawn_isolated_with_args_kind(kind, closure, d1, d2)` exist in both
  `executor.rs` and `runtime_thread.c`, and are renamed under
  `SIMPLE_RUNTIME_THREAD_RUST_OWNER`.
- The unsuffixed Simple-facing entries (and Rust `rt_thread_spawn_limited*`)
  are fixed to kind VALUE. Their Simple extern names are unchanged, so deployed
  interpreters keep working. The contract is documented at the externs in
  `concurrent/thread.spl` and `sffi/concurrent.spl`.
- Removed: `native_closure_payload`, `native_resolve_ambiguous_word`,
  `native_candidate_is_callable`, and `NativeWordForm` from Rust, and the
  spawn-path use of `rt_native_closure_payload` from C.
- C parity: the single-argument C worker now honours the raw-argument ABI, as
  Rust does. Before, C passed tagged args to raw workers: the probe returned
  280 instead of 42.

**TDD evidence (Windows x86_64, clang-cl, own CARGO_TARGET_DIR, --release --lib).**
- Before (old `executor.rs` with the new legacy-entry fixtures): both tests
  FAILED, every time. `test_before_dual_decodable_value_word` failed with
  "VALUE spawn of dual-decodable word 0x80180000 rejected". The legacy-entry
  stress (16 x 64 = 1024 spawns) also failed: 8 spawners rejected that word.
- After: `executor|thread|worker_closure` 37/37. `isolated_thread|worker_closure`
  passed 17/17 on 20 of 20 runs. Each run has two 1024-spawn stress specs, so
  that is 40,960 stress spawns with 0 failures. Full `--lib`: 1394 passed. The
  2 failures are `pty` ConPTY resize and symlink canonicalize, which do not
  touch the executor.
- C lane: `windows_thread_code_dispatch_test.c` passed 200/200 and
  `rt_thread_owner_contract_selfcheck.c` passed 200/200 (clang + lld). Both are
  linked directly against `runtime_thread.c`. The script lane
  `check-rt-thread-owner-contract.shs` fails at link on a duplicate
  `rt_time_now_seconds_f64` that already exists on the base. That failure
  happens before this change, and the change did not cause it.
- New specs: `test_worker_closure_kind_decode_is_explicit` covers every
  kind/tag branch at the bug site. Also added:
  `..._value_int_tagged_record_selects_raw_abi_at_any_address`,
  `..._value_heap_tagged_record_keeps_runtime_value_abi`,
  `..._classifier_follows_kind_not_value`,
  `..._dual_decodable_word_follows_declared_kind`,
  `..._explicit_kind_stress_concurrent_spawners`,
  `..._legacy_value_entry_stress_concurrent_spawners`, and
  `..._unmapped_word_fails_closed`.

**Similar-pattern audit.** The grep covered `src/runtime` and
`src/compiler_rust/runtime/src`, looking for VA ceilings, `>= 4096 && & 7 == 0`,
and "looks like a pointer" logic.
- Pool function-value decode (`runtime_pool.c` and pool-v1 in
  `runtime_thread.c`) uses the same value-based rule. Filed as
  `pool_native_function_payload_value_heuristic_2026-11-06`.
- `value/core.rs:595` checks `is_registered_heap_ptr`, a registry lookup
  rather than a guess. No change needed.

**Still pending verification:** Linux and aarch64 runs, the board run, and a
native-compiled Simple `thread_spawn_with_args` smoke
(`check-thread-spawn-with-args-native.shs`). That smoke needs a seed that can
link native binaries on this host.

## Windows current-source C verification (2026-11-10)

At `release/1.0.0` source `6d496f82c5acabc2fc52b2b78146272e664dc371`,
LLVM clang 23.1.2 targeting x86_64-pc-windows-msvc compiled and ran
`windows_thread_code_dispatch_test.c` successfully (exit 0). This direct
dispatch fixture includes the real thread owner and explicitly supplies an
empty registered-closure fixture; it does not qualify registered heap closures.

The canonical `check-rt-thread-owner-contract.shs` also passed (exit 0):
42 current core-C objects linked, and `rt_thread_owner_contract_selfcheck`
executed successfully. It covers one/two-argument explicit kinds, invalid
kinds/tags, handle lifetime, and 2,048 pool tasks with dual-decodable words.
The historical duplicate-timestamp-symbol link failure above is not present
in this source composition. Both checks ran once; no unchanged PASS was rerun.

Exact commands, source/binary identities, and result scope are in
[the SDN receipt](evidence/20261110/p0_thread_runtime.sdn). No runtime source
was changed for this verification. Status remains
**fix-implemented-verification-pending**: Linux, aarch64, board execution,
and the native-compiled Simple smoke are still unexecuted. Ubuntu WSL failed
to start with `Wsl/Service/CreateInstance/E_FAIL`; no Linux result is inferred
from that installed distribution. The Simple smoke requires a proven native
compiler/runtime; a Rust-seed result cannot establish self-hosted qualification.
