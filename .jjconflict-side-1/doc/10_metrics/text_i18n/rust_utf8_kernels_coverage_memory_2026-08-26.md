# Rust UTF-8 kernels coverage and memory — 2026-08-26

Stable LCOV supplied no branch denominator, so authoritative branch evidence
uses installed nightly Rust with `cargo llvm-cov --branch`.

| Cycle | Tests | Branches | Lines | Result |
|---|---:|---:|---:|---|
| 1 | 4/4 | 30/48 (62.5%) | 276/313 | baseline |
| 2 | 4/5 | incomplete | incomplete | exposed `NIL` typed-ingress defect |
| 3 | 5/5 | 49/52 (94.23%) | 395/404 | final bounded cycle |

The fix checks heap object type before runtime byte-array or text conversion;
`NIL`, strings passed as arrays, non-integer elements, and values outside
0–255 now fail closed.

The current width index reserves 131,072 bytes for 16,384 scalars in a 36,864
byte source: 8.00 bytes/scalar before HashMap/mutex/allocator overhead. Eight
threads complete 512 build/query/free lifecycles and restore registry length to
baseline. This proves reclamation only, not sparse/succinct memory efficiency.

Criterion `simd_utf8_validate` on 656 KiB mixed-valid input:

| Tier | Time interval | Central throughput |
|---|---:|---:|
| scalar | 478.99–488.39 us | 1.21 GiB/s |
| x86-64 AVX2 | 458.28–499.18 us | 1.23 GiB/s |

The AVX2 result is consistent with ASCII-prefix scanning plus scalar validation,
not a complete vector kernel. Three defensive typed-object corruption branches
remain unexecuted; no 100% owner claim is made.
