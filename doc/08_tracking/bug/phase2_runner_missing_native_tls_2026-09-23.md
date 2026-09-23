# Phase2 runner missing native TLS provider

Status: focused native fix verified; full Phase2 runner admission remains pending.

At source `2710d948270316e156a0f90380b28adedb2e801f`, the dedicated
test-runner link failed on `rt_thread_local_new` in the MC/DC dynamic-probe
module initializer. The retained `mod_558.o` also references get/set. The
canonical Simple owner (`std.nogc_sync_mut.runtime.thread_local`) declared
four raw-i64 hooks, but only the Rust tagged-value runtime implemented them.
The allowed host-gpu/core-C composition has no Rust-hosted fallback.

## Ownership and contract

Implement the complete four-hook ABI in existing K0 `runtime_thread.c`, already
listed by both the core capsule builder and native runtime compiler. This adds
no optional bundle, new provider dependency, or platform-specific static library.
OS-specific optional functionality continues to belong to dynamic providers.

Unset, invalid, cleared and freed raw-i64 slots return zero, as required by
MC/DC slot+1 and RT-HAL worker registration. The Rust interpreter's tagged NIL
(`3`) is a different value representation and is deliberately not copied.
All signed-i64 payloads round-trip. Zero clears. Payload ownership stays with
the caller; free never destroys caller-owned pointers.

The provider has 128 live slots. Allocation returns zero on exhaustion.
Generation-tagged positive handles reject stale accesses after slot reuse and
retire on overflow. New/free use the existing registry lock. Get/set use an
acquire active-handle check and thread-private values; that check linearizes
operations overlapping free. Old per-thread bits cannot match a new generation.
Fixed native storage costs 2048 bytes per thread and 2048 global bytes, without
growing maps or per-value heap allocation. Thread exit releases native TLS.
Native TLS allocation and atomic lock-freedom remain platform-dependent.

## Evidence

Evidence directory in isolated worktree:
`build/native_probe/thread-local/`.

- `sh scripts/check/check-runtime-thread-local.shs`: PASS, including invalid
  handles, full-width signed values, clear, thread isolation, global invalidation,
  stale free/set, 128-slot exhaustion, 100000 reuse cycles, concurrent free/use,
  last permitted generation and retirement. The intentional negative control
  fails as expected. Final UBSan run: PASS, 0.65 seconds compilation plus run,
  69,500,928-byte peak RSS including compiler. No sanitizer diagnostics.
- Admitted producer SHA256
  `fc2fc3a280ed6afc056ac766a7561a0ba5d6d57038bc8bbb33ea474d9f6a4930`
  emitted `test/fixtures/native/thread_local_boundary.spl` as an archive through
  the admitted compiler's Rust-delegated native archive route, with
  `SIMPLE_NO_STUB_FALLBACK=1`, one build thread and isolated cache. This is
  focused Stage2 evidence, not final self-hosted/compiler-suite admission.
- The emitted archive linked against the original Phase2 core archive fails
  on all four TLS symbols (`simple/red.log`). Adding the new provider object
  yields `Simple TLS boundary: PASS` (`simple/run.log`). Build sampled peak
  59,376 KiB; run sampled peak 2,544 KiB; enforced cap 5,859,375 KiB. No claim of
  kernel hard memory containment or speedup.
- Original retained MC/DC `mod_558.o` plus new provider object passes native
  relocatable link; `retained-probe.o` defines all four TLS hooks and has no
  unresolved TLS hook. This is not a full runner relink.
- ASan could not initialize on this host: stack sample shows dyld malloc zone
  initialization reentering AsanInit before main. The owned test was terminated
  after 57 seconds; `sanitized-sample.txt` retains the stack. No ASan success
  or application leak-freedom claim is made.
- Working direct-env guard: PASS. Executable specs under `doc/06_spec`: zero.

Artifacts: native boundary archive SHA256
`b4568f6dea53e016bf0c27c130ba0b8f2b536f6a09e56619858dff51aa5f702a`;
native boundary executable SHA256
`f685c4dd28c9a759261b3cec94ad1cf421f8f843a9d94290b20b30b7275191e0`.

Independent Astra design review accepted the ownership and generation model.
Final independent review passed implementation and revised C tests. The native
Simple fixture is deliberately invoked explicitly rather than discovered as an
interpreter SSpec, because the interpreter uses a different tagged-value ABI.
Integration must rebuild the phase runtime capsule from the new source and
complete the full runner/compiler tests before Stage3 admission. Windows and
Linux execution are not claimed by this macOS evidence.
