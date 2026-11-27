# C4 hosted scope reader: unconditional admission-index overhead

Date: 2026-10-25
Status: OPEN — bounded, measured local cost; full compiler comparison pending.
Owner: hosted Rust RuntimeDict provider.

The bounded reader cannot use the existing allocation HashSet directly:
its public membership operation does not expose a fuel-limited probe loop.
The provider therefore maintains a second lifecycle index for real Dict,
String and boxed signed-Int allocations, including programs that never query
a scope. Registration/free acquire its mutex. Dictionary mutations enter and
leave a reader-exclusion marker under that mutex.

This is an intentional additional cost, not zero-cost instrumentation. The
16-byte admission slots grow at 75% occupancy. Dictionary-only descriptors
hold owner generation, epoch, opaque backing token, actual storage pointer,
actual slot capacity and mutation depth. A freed descriptor is reused with
a fresh generation. The hash table retains its high-water allocation after
frees, as does the existing canonical heap registry.

## Measured diagnostic evidence

Isolated base: `75d260930c3`; command:

```text
cargo test -p simple-runtime --lib scope_read --no-default-features --features runtime-symbol-table --target-dir /tmp/c4-scope-read-rust-cargo-20261025 -- --test-threads=1 --nocapture
```

Cycle 5 log: `/tmp/c4-scope-read-rust-cycle5-20261025.log`.
These are Rust runtime tests on the current Linux host, not self-hosted
compiler, interpreter-HashMap, SPipe, native C, or SOURCE acceptance evidence.

| Observation | Result |
|---|---:|
| Relevant focused tests, including symbol table ownership | 8 passed |
| 100,000 reads, 4,097 bindings | 2,261 microseconds; 0 allocator calls |
| Construct 65,537 bindings | 41,512 microseconds |
| Replace a binding 100,000 times | 4,374 microseconds |
| Scan 131,072 physical slots | 5,736 microseconds; 0 allocator calls |
| Retained admission slots | 131,072 |
| Admission slots plus dictionary descriptors/free list | 2,097,376 bytes |
| Linux runtime-test process max RSS | 185,640 KiB |
| Sparse-live allocation/free churn | 20,000 operations; 35 max absent lifecycle probes |

The RSS includes the entire runtime test harness and its initialization;
it is not an attributable reader RSS delta. No before/after constructor or
whole-compiler latency comparison was performed. Earlier local prototypes
used 40-byte slots at 50% occupancy; separating dictionary metadata and
raising occupancy reduced the measured index from 4.19 MB to 2.10 MB.
Used-slot accounting includes tombstones; deletion-heavy load compacts at the
current capacity, and unrelated heap kinds bypass this index on free. The
reader's 64-probe ceiling never truncates lifecycle removal.

The deterministic ABA test unregisters/re-registers the same real allocation
through the private lifecycle hooks. It does not claim that the allocator
was observed to recycle a freed address. Actual freed handles and keys are
separately checked. The selected self-hosted compiler's typed facade/query
has not been executed by this Rust-only lane; interpreter HashMap backing
remains unsupported.

## Follow-up and acceptance

1. Measure the same real compiler fixtures against the unmodified provider:
   startup time, allocation/mutation throughput, HIR construction time, peak
   admission capacity, total allocation bytes and max RSS.
2. If material, unify bounded membership and the canonical heap registry
   under one owner rather than maintaining two allocation indices. Preserve
   the existing validation cache, byte counters and every generic free hook.
3. Retain all owner/ABA, overflow, collision-tail, storage-authority, type,
   order, mutation-exclusion and zero-allocation regression controls.

Do not claim negligible ordinary compiler overhead, a fully measured source
storage seal, or release readiness from the read timings above.
