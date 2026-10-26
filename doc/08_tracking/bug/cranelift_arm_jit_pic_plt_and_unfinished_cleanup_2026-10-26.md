# Cranelift ARM JIT PLT abort and unfinished-builder cleanup

Status: focused provider regressions PASS at `71297cb813f`; independent source
review GO. Scope is the actual Rust
Cranelift SFFI provider, not bootstrap/tool admission. No AOT, Phase 3, or full
compiler qualification follows from this record.

## Observed failures

The SOURCE backend propagates function errors to its module owner, which calls
`cranelift_free_module`. Provider `retire_exposed_handles` and registry reset
called `FunctionBuilder::finalize()` while discarding unfinished IR. Cranelift
requires filled/sealed blocks during finalization. Cancellation must instead
drop the borrowing builder before dropping `BuilderBacking`; normal successful
`rt_cranelift_end_function` remains the finalization boundary.

The first focused test build at `268129dcef0` executed zero tests: its new test
module incorrectly inherited an x86-only gate on an AArch64 host. The corrected
`d8f6202d32b` harness listed exactly four tests, but its first test aborted in
`rt_cranelift_new_module` before cancellation was reached. The actual diagnostic
was `PLT is currently only supported on x86_64`, from vendored Cranelift JIT
`backend.rs:297`. This was a preexisting constructor bug exposed by the fixture,
not a cleanup-test pass.

Evidence is retained under `/tmp/cranelift-abort-execution-20261026` (zero-case
failure) and `/tmp/cranelift-abort-execution-arm-20261026` (ARM SIGABRT). The latter
binary SHA-256 is
`f6bb61a24974ffc7257fb8166db8b06fa55e5296b3a712ee4b6c33c3c9dd35ac`.

## Root cause and minimal correction

The provider shared an ISA with `is_pic=true` between AOT and JIT. In the local
Cranelift 0.116 dependency, `JITBuilder::with_flags` sets both
`use_colocated_libcalls=false` and `is_pic=true`; PIC false is **not** its default.
However, `JITModule::new` preallocates libcall PLT entries whenever PIC is enabled,
and the PLT writer asserts that the host is x86-64. Its explicit non-PIC path
skips these entries. The provider does not enable hotswapping, which requires PIC.

A dedicated JIT ISA helper therefore keeps PIC on x86-64 and selects the
supported non-PIC path on other native architectures. It retains speed settings
and target stack probes and explicitly disables colocated libcalls, as required
by the JIT contract for long-range relocations. Foreign-architecture JIT requests
return the existing failure sentinel before constructing a native JIT module.
AOT retains its existing PIC settings and cross-target support unchanged.

All four cancellation regressions remain real provider tests, run serially due
to whole-registry reset. They cover unsealed/partial builders, JIT and AOT cleanup,
repeated/stale module handles, other-module isolation, and successful native JIT
execution returning 42. The fixture checks effective JIT/AOT settings and refusal
of a foreign JIT architecture. It does not skip ARM or claim unsupported success.

## Bounded combined attempt ledger

The original cleanup lane and new constructor prerequisite share one conservative
six-cycle ceiling; identifying a new cause does not reset it.

1. `d9ad2eb7967`: initial cancellation API proposal; source review found no new
   ownership issue but whole-module cleanup made the export unnecessary.
2. `268129dcef0`: minimal existing-boundary cleanup; source review GO. New ABI
   removed, exact SFFI audit migration delta returned to zero.
3. Execution of `268129dcef0`: zero tests, **FAIL**, 62 seconds compile,
   1,187,504 KiB sampled peak, quiescent. No behavior criterion accepted.
4. `d8f6202d32b`: test-only architecture correction; source review GO.
5. Execution of `d8f6202d32b`: exact four-name inventory, then ARM constructor
   SIGABRT; zero completed tests, **FAIL**, 428,872 KiB sampled peak, quiescent.
6. `71297cb813f`: dedicated JIT-profile correction, independent source GO,
   and root-admitted final batch. The harness listed the exact four expected
   names before execution; **4 passed, 0 failed, 0 ignored**, including native
   ARM execution returning 42. Compile took 1.39 seconds; tests 0.02 seconds.
   Sampled peak was 443,284 KiB under the 2 GiB cap; exit 0, quiescent 1,
   `hard_memory_limit=0`. No seventh cycle or repeated green test followed.

Final evidence: `/tmp/cranelift-abort-execution-final-20261026/result.sdn`,
with command, admission, inventory, compile/test logs, and watchdog receipt.
Final tested binary SHA-256:
`43462c24c316d1458b64494b46daf5aab9aab444220fe094646b64923bf64e49`.
The two earlier failed attempts remain failures and are retained separately.
This result checks the provider cancellation/JIT prerequisites only; it does not
execute the new SOURCE backend path or admit Phase 3.

Prior 18 allocation-claim, five P0, and seven P1 passing tests are unrelated and
were not repeated. The SFFI audit still fails its existing baseline limits
(411 source variants / 399, 3730 migrations / 3546); the final cleanup introduces
no new export or migration item, and no ceiling or waiver was added.
