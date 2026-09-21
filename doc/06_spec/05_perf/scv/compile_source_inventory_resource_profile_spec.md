# SCV cold inventory resource profile

Executable specification:
`test/05_perf/scv/compile_source_inventory_resource_profile_spec.spl`.
Native workload: `test/fixtures/scv_inventory_memory/profile.spl`.
Collector: `scripts/check/check-scv-inventory-resource-profile.shs`.

This manual accompanies authored executable assertions. Native execution is
blocked by the admitted producer's MIR crash; it is not PASS evidence.

## Scenarios

| Workload | N / 2N | Compared with | Assertions |
|---|---|---|---|
| Scoped per-file event construction | 256 / 512 | Unscoped construction with identical file reads and retained events | Every event field remains valid after scopes end; identical five-facet digest; elapsed <= 1.5x baseline + 20 ms; N/2N elapsed <= 3x + 20 ms |
| Initial batch reduction | 512 / 1,024 | Sequential create reduction of identical reversed events | Sorted identities, correct count/generation, complete encoded-inventory digest equality; elapsed <= sequential + 20 ms; N/2N elapsed <= 3x + 20 ms |
| Native compilation of the fixture closure | One clean compile | Absolute admission budget | Successful native executable, peak RSS strictly below 1,000,000,000 bytes, elapsed < 180 s |

Each runtime workload runs in a fresh process. Every peak must be positive and
strictly below 1 GB. Scoped/batch peak RSS may exceed its baseline by at most
16 MiB, and its N/2N growth may exceed baseline growth by at most 8 MiB. These
are regression tolerances, not claims of a measured memory reduction. Baseline
growth is reported even when allocator noise makes the difference negative.
Internal elapsed measurements exclude post-run digest verification and, for
reduction, identical input construction. Peak RSS includes the whole process.

Both hashing modes additionally record the exact `rt_heap_registry_count`
delta around event construction, before printing or post-run assertions.
At both sizes the scoped route must retain less than half the unscoped live
objects. This has no RSS or timing allowance: the original unscoped retention
mutation leaves the same scratch registered and fails. A positive count is
mandatory, so a missing/stubbed counter cannot pass. The native unit spec
`test/01_unit/lib/scv/compile_source_inventory_reclamation_spec.spl` warms
literal caches, compares both routes, and includes an unscoped-versus-unscoped
negative control for the same reclamation predicate.

The collector verifies parent schemas and supported authority, then invokes
the canonical `bootstrap_stage3_verify_stage2_admission_receipt` validator.
This binds the candidate path/hash, source/tool snapshots, frozen runtime,
ABI policy, sanity/receiver evidence and companion logs. Parent snapshot hashes
must match the admission, and the requested producer must match the admitted
candidate. `--admission-only` runs that validation without executing a compiler.
It bounds compilation to 180 seconds and
each workload to 60 seconds, preserving stdout/timing logs in a unique
`build/scv-resource-profile.*` directory. A crash, timeout, missing completion,
duplicate field, invalid number, empty digest, or absent memory measurement
cannot produce a passing SSpec. No checked-in historical metrics are consumed.

## Run

With an admitted pure-Simple Stage 2 producer and a self-hosted CLI that supports
`test`, export `SCV_PROFILE_COMPILER` to the Stage 2 executable and run:

```sh
<self-hosted-test-runner> test test/05_perf/scv/compile_source_inventory_resource_profile_spec.spl --mode=interpreter
```

For diagnostics without a test-capable producer, run the collector directly:

```sh
SCV_PROFILE_COMPILER=/absolute/admitted/stage2/simple sh scripts/check/check-scv-inventory-resource-profile.shs
```

Collector completion alone is not a passing SSpec. This focused native compile
also does not qualify the full jobs=8 Stage 3 build.

## Validation on 2026-09-21

Producer SHA-256:
`e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`.
All adjacent receipts and the admitted hosted archive matched their hashes.

1. Initial isolated-checkout compile failed package index admission before
   HIR: `scv-authority-missing`, elapsed 2.55 s, peak RSS 445,546,496 bytes.
2. After explicitly enabling `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, the native
   compile reached HIR for 27 modules and monomorphization, then exited 139 in
   MIR. Elapsed was 7.27 s; peak RSS was 883,605,504 bytes. Diagnostics included
   `malformed_hir_type` and qualified-name field-list collisions involving
   `lib.nogc_sync_mut.io.process_ops::...OwnedProcessLease`.

The below-budget failed compile is not successful memory qualification. No
native workload executed. Shell syntax and the collector help path passed;
the refreshed self-hosted test runner is still needed for the complete SSpec.

### Review corrections

Five synthetic negative receipt cases (missing schema, unsupported authority,
wrong candidate, wrong runtime and missing sanity evidence) all returned exit 1
before their sentinel producer was invoked. They are exercised by
`test/01_unit/lib/scv/compile_source_inventory_profile_admission_spec.spl`.
The supporting negative fixture itself executed successfully; the SSpec runner
remains unavailable.

Canonical admission replay of the formerly selected producer now refuses its
sanity version binding: the receipt records `1.0.1-beta.1`, while this remote
checkout's canonical version is `1.0.0-beta.14`. No new compile was attempted.
The preceding MIR attempt used the earlier incomplete collector checks and is
diagnostic history only. Live-object reclamation and its mutation control are
authored pending a producer that passes full admission and supports execution.
