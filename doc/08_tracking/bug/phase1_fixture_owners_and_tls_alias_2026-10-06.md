# Phase 1 fixture owners and TLS label conversion

The diagnostic producer is seed SHA-256
`0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`,
using frozen source `e59027c353e9ed6ea8ddf572424da70e188fe511` with isolated
owner repairs. This is selected Phase 1 evidence, not whole-phase or release
qualification.

| Repair | Actual original assertions passing |
|---|---:|
| Zstd rotate fixture imports the surviving xxhash owner | 3 |
| Nil-contract fixture uses current JSON/date owners | 7 |
| Context sharing restores its docstring and real reusable fixtures | 13 selected failures |
| Byte/text guard uses the surviving uniquely named converter | 3 |
| YAML fixture uses current module owners | 4 |
| Config parser exposes its two original examples at top level | 2 |
| TLS wrapper calls the uniquely named crypto label converter | 1 selected failure |

The TLS full baseline passed 20 examples and failed its unchanged 100-byte
wrapper vector. The selected failure reproduces with the original owner and
passes after replacing the ambiguous alias with `crypto_text_to_bytes`.
The 20 green examples were not repeated. The general co-compiled alias collision
remains a compiler issue; this uses the already documented unique owner API.

Context sharing first passed four cases after fixing only its docstring, then
the remaining 13 passed after restoring the actual fixtures. The final full
17-case file was not rerun. An import-only config-parser attempt produced no
individual examples and was rejected; the accepted repair executes two named
assertions. All expected values/error oracles are retained.

Raw evidence and producer bindings: `/tmp/simple-phase1-xxhash-repair/evidence.md`
and its referenced logs, actual runner result artifacts and RSS receipts.
The separate SHA3 JIT diagnostic remains failing and is excluded from these
repairs and pass counts.
