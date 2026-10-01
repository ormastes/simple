# GPU MMU Explicit Residency and Placement

> **Status: GENERATION AND EXECUTION PENDING.** This is an honest manual mirror
> of the executable SSpec source, not PASS evidence. On 2026-07-31 the canonical
> pure-Simple `bin/simple` identified itself as `simple-bootstrap 1.0.0-beta`
> and rejected `test`, `check`, and `spipe-docgen` as unknown commands. The only
> located pure-Simple Stage 2 candidate with `check` has no test/docgen surface;
> Stage 2 is not admissible SPipe evidence. The Rust seed was not used.
> Its diagnostic parser also rejected the ordinary `_chunk` `while` loop in the
> RSS probe at line 30 (`unexpected token ... while`); after the mandatory third
> diagnostic cycle this remains unverified rather than being papered over with
> a source workaround for the stale Stage 2 parser.

Executable source:
`test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl`

Linux RSS probe:
`test/03_system/lib/gpu/object_vm/gpu_mmu_rss_probe.spl`

## Purpose and claim boundary

This scenario exercises the portable GPU Object VM, crash-safe CAS, placement
planner, bounded staged backend, optional direct parity, and experimental
device-initiated gate. Direct hardware absence must remain `unsupported`.
Measured RSS is accepted only from Linux `/proc/<pid>/status` `VmHWM` collected
in isolated 1x and 10x probe processes; the deterministic allocation model is
reported separately and cannot substitute for that measurement.

## Operator flow

1. **Create arena handles and acquire a lease**
   - Create one arena-granularity descriptor and entity handle.
   - Resolve its byte/entity counts, acquire an epoch-bound resident view, and
     read a known byte only through that lease.
   - Covers REQ-001 and REQ-002.
   - A folded consumer scenario constructs the actual parser input/output and
     linker input/output ports, then verifies their `ArenaResidency` object
     slots, generations, entity counts, byte lengths, and `EntityRef` values.
   - The same scenario binds actual structural-layout input, browser style and
     layout results, and Draw IR WebScene output to typed arena residency and
     verifies each retained field. Covers REQ-009 without a synthetic proxy.

2. **Reject stale handles and protected eviction**
   - Verify an active lease and a pin each reject eviction as `protected`.
   - Release the lease and observe `stale-lease`; destroy and reuse the slot and
     observe `stale-handle` for the old generation.
   - Issue the same cold residency miss twice and observe `miss-started` then
     `miss-coalesced` before completion.
   - Covers REQ-002 and REQ-003.

3. **Stage an artifact through the bounded pinned ring**
   - Use canonical structural `ArtifactId(content_hash, schema_version)`; CAS
     assertions separately verify canonical `CasBlobId(digest, byte_len)`.
   - Verify an eight-byte retained/high-water bound on every host.
   - When only the heap-backed USM fixture is available, require the explicit
     `usm-malloc-host-is-heap-backed` simulation capability before checking
     three-transfer slot rotation and exact byte readback.
   - When CUDA pinned USM is available, allocate a device buffer and require a
     completed `staged_cuda` receipt after host-to-device, synchronization,
     device-to-host verification, and synchronization.
   - Covers REQ-004 and supports NFR-001.

4. **Recover the CAS after interrupted or corrupt writes**
   - Commit and reopen one immutable blob/manifest binding.
   - Independently inject a partial journal tail and corrupt a referenced blob;
     both reopen attempts must fail with a `gpu_cas:` error.
   - Covers REQ-005 and NFR-004.

5. **Plan placement from liveness cost and budgets**
   - Submit two frozen `PlacementRequest` values twice and verify the same
     concrete reservation, transfer, eviction, prefetch, lease, 15 us predicted
     cost, and 64-hex receipt seed.
   - Covers REQ-006 and NFR-003. Fixed-workload calibration is measured in the
     RSS step rather than fabricated from constants.

6. **Compare staged and direct backend bytes**
   - With the CPU parity fixture enabled, require independently retained staged
     and direct receipts to carry the known checksum `4:100:300` and status
     `simulated` with reason `cpu-payload-parity-only`.
   - With capability absent, require `unsupported` and
     `direct-hardware-unavailable`, never staged fallback reported as direct.
   - Covers REQ-007 and NFR-006.

7. **Keep device-initiated placement behind its gate**
   - Require `device_initiated` to remain unavailable with reason
     `experimental-gate-disabled` when its explicit flag is off.
   - Verify staged routing reports bounded heap simulation on non-CUDA hosts or
     production `staged_cuda` only when the pinned/device-transfer facade is
     available.
   - Covers REQ-008.

8. **Measure the fixed host RSS bound**
   - Run the standalone Linux probe in isolated processes for 4 and 40 chunks
     using the same four-slot 256 KiB staged ring.
   - Require `VmHWM` to remain within each measured runtime base plus fixed
     staging, driver/queue, and manifest-cache budgets; require the 10x run to
     reach, but not exceed, the fixed staging high-water bound.
   - Separately require the hot descriptor metadata contract to equal 40 bytes
     and the allocation model to remain corpus-independent.
   - Record elapsed microseconds for the fixed 40-chunk EXEC workload. Compare
     it with the plan's 15 us prediction under a stated 1,000,000 ppm bound,
     then prove a deliberately narrow 1,000 ppm gate rejects the same observed
     workload.
   - A missing Linux `VmHWM` produces `unsupported`, not PASS.
   - A staging execution error produces `fail`, not `unsupported`.
   - Covers NFR-001, NFR-002, NFR-005, and NFR-007.

## Resume commands

After a current pure-Simple full CLI is deployed, run each command once:

```sh
SIMPLE_BINARY=/path/to/admitted/simple /path/to/admitted/simple test test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl --mode=interpreter
/path/to/admitted/simple spipe-docgen test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl --output doc/06_spec --no-index
/path/to/admitted/simple md-diagram-update doc/06_spec/03_system/lib/gpu/object_vm/gpu_mmu_spec.md
```

Acceptance requires the test runner's authoritative final result, docgen
completion with `0 stubs`, and independent review of the regenerated manual.
Until those exist, this document remains generation pending.

REQ-004 is no longer a placeholder gate: CUDA hosts must produce and verify a
production transfer receipt, while non-CUDA hosts must explicitly identify the
bounded heap simulation. Runtime execution remains pending until the admitted
pure-Simple CLI is available.

## Traceability

| Contract | Evidence step |
|---|---|
| REQ-001, REQ-002 | Create arena handles and acquire a lease |
| REQ-009 | Folded parser/linker/layout/style/WebScene residency scenario under Create arena handles and acquire a lease |
| REQ-002, REQ-003 | Reject stale handles and protected eviction |
| REQ-004, NFR-001 | Stage an artifact through the bounded pinned ring |
| REQ-005, NFR-004 | Recover the CAS after interrupted or corrupt writes |
| REQ-006, NFR-003 | Plan placement from liveness cost and budgets |
| REQ-007, NFR-006 | Compare staged and direct backend bytes |
| REQ-008 | Keep device-initiated placement behind its gate |
| NFR-001, NFR-002, NFR-005, NFR-007 | Measure the fixed host RSS bound |

## Executable mechanics

The complete modern SSpec source remains authoritative at the executable path
above. It uses `std.spec.*`, direct value assertions, built-in matchers, the
frozen public contracts, and no placeholder pass. Regeneration must replace
this pending mirror only after the executable scenario actually runs.
