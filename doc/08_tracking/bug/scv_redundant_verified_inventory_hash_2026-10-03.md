# Redundant hash on validated immutable inventory reads

The immutable generation reader hashes the bounded blob and compares it with the captured pointer. Its decoder then validates canonical re-encoding and hashes the exact same blob again to return the digest. For the retained Windows qualification inventory this blob was16,941,026 bytes/44,286 rows. This establishes redundant work, not its share of the measured630-second cold publication window or the later1200-second p2_add timeout.

The performance-only fix passes the verified pointer to a private decoder. Public decoding still computes its digest, and all syntax, canonical re-encoding, regular-file, size, pointer, and immutable blob hash checks remain. No persistence format, errors, source membership, or publication policy changes. PR2271 warm no-event refresh and PR2284 flat-pool serialization repairs are already in this branch's base and are not duplicated.

Focused regressions cover public/read equivalence, changed canonical bytes, and digest-matching noncanonical bytes. SSpec execution remains UNRUN: this host has no admitted self-hosted Windows runtime. The optimization CLI and required core/MCP runtime checks are likewise BLOCKED. Old candidates, failed receipts, and caches are unchanged.

## Paired bootstrap diagnostic

The bounded three-cycle diagnostic retained failed harness attempts, compiled two exact reader projections with the original C52/Rf21 LLVM bootstrap tuple and 80 build workers, and collected five fresh samples per variant against the same retained inventory. Cycle 3 reused both completed builds and the first passing baseline sample; it executed only the remaining nine samples. All ten count/digest outputs, collector status/hash/bounds/cleanup, executable identity, mandatory RSS, and source/runtime/tool authority pins passed terminal integrity verification. This is provisional diagnostic evidence, not SSpec or product admission.

| Metric | Baseline | Fixed |
|---|---:|---:|
| p50 process elapsed | 9.478 s | 9.915 s |
| p95 process elapsed | 10.510 s | 11.135 s |
| Peak sampled RSS | 229016 KiB | 211856 KiB |

Time ratio1.05944, memory ratio0.92507, sum1.98451. Peak sampled memory decreased7.49%; p95 elapsed increased5.94%. Elapsed includes the identical environment/RSS/collector wrapper, and the small combined margin is not established beyond measurement noise. Joint resource acceptance remains UNPROVEN; no speedup or1200-second timeout cure is claimed. The diagnostic feature's three cycles are exhausted; no fourth measurement or old qualification replay is permitted without a new explicit exception.

Evidence: `C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/scv-verified-digest-performance3/{paired-performance.json,terminal-validation.json,benchmark.receipt.env}`. Outer receipt SHA00dd918da840fc4674b6ec9620c8ec9e879f18ad2cab2e37b9314fa815480a86; log SHA6b7096f1622eda3cb5d7eec7716131e914795f26936fdc0e2bf7cfe786550eec.
