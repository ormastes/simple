# Runtime array join truncates counted strings at NUL

Status: focused C-owner repair qualified on Linux SOSIX; compiler integration and other platforms unexecuted.

`rt_array_join_any` converted registered counted strings to C pointers then called
`strlen` for sizing and copying. A three-byte `a\0b` item followed by `cd`, joined
with comma, produced four bytes `a,cd`; the counted `rt_string_join` produced the
correct six bytes. Tagged separators also lost bytes after NUL. The old sizing
loop additionally did not guard total allocation overflow.

The repair resolves each registered string using its stored length and preserves
borrowed NUL-terminated literals, including unaligned/tag-like addresses. Small
non-text values retain the prior empty contribution. Arbitrary non-text heap
objects and invalid raw pointers remain unsupported inputs. Both passes borrow
inputs; result registration, nil on registration failure, and empty string on
allocation/size failure remain unchanged. Each addition reserves header and NUL
space. No scope, lifetime, global allocator or runtime ABI is changed.

## Source and real owner evidence

Source base: `da05a87f6fc3418e54ac813ba7aad97c35bce4f5`.
The current complete translation unit and the historical complete owner both
compile with the admitted Linux owner1 flags. Historical source starts from the
already qualified bounded-reader/empty-scope runtime. The identical join region
was replaced only after exact original-region equality assertion.

Artifacts: `/mnt/c/Temp/simple-runtime-join-nul-20261012`.
`cycle1.json` retains actual compiler/link commands and baseline19/candidate23
real assertions. `cycle3.json` retains the independent registry-calloc failure
case: both owners fail after 178 retained joins and free the rejected result
exactly once. Test source is `src/runtime/test/array_join_counted_selfcheck.c`.
Cases cover empty/singleton/mixed raw and tagged strings, nonASCII, NUL items and
separators, all eight raw address alignments, nil/small values, trailing sentinel,
input preservation, malloc failure, and size overflow rejected before allocation.
Overflow tests temporarily alter actual registered metadata, restore it before
free, and never run unsafe overflow against the baseline. No huge allocation is
attempted. Existing passing assertions were not rerun.

Baseline archive SHA256:
`07a41f222989ede29bb472d1826627189151e6829f35f491f8c4d4ca2198c0fb`.
Candidate archive SHA256:
`47a386651d02839e9ec1cf86c41728105e827ce32d6f5fbef32497582f9d7993`.
Paired compiler backfill SHA256:
`935f72674326bbf1042d4c4ce8bfdb1fccf4796242e8a418db65d7744a3ac723`.
`archive-audit.json` confirms exactly runtime_native.o changed, all 40 members
retained, and defined global symbols unchanged. `source-identities.json` binds
source, fixture, objects and archives. No synthetic cache admission or stubs.

## Latency and memory bounds

Linux SOSIX microfixture: 512 items of 1024 bytes, 8192 joins per process, 11
alternating baseline/candidate samples. Assertions validate length and boundary
bytes on every join. `perf-samples.json` and `perf-summary.json` retain samples.

| Input | Baseline p50/p95 seconds | Candidate p50/p95 seconds | Peak KiB baseline/candidate | Steady after max KiB baseline/candidate |
|---|---|---|---|---|
| Tagged | .122587/.160117 | .092757/.099363 | 2944/2920 | 2944/2920 |
| Raw | .085227/.116139 | .084766/.095399 | 2912/2912 | 2912/2912 |

Both allocate exactly 8192 result buffers totaling 4,299,292,672 bytes over the
loop; buffers are released each iteration. No additional per-item allocation.
Peak and steady remain below the independent 8MiB budget; p95 below .25 seconds.
Tagged time ratio .621, memory ratio .992; raw time ratio .821, memory ratio1.
These are microfixture observations, not compiler throughput or leak-freedom.
Initial cycle1 getrusage peaks inherited the Python launcher and are discarded;
cycle2 uses /proc/self/status VmHWM and statm. The measured executables were later
relinked for the final failure-injection case; archive/object identities remain
fixed, but the earlier harness binary itself was not retained. Three cycles used;
no further test-runner or compiler rebuild was attempted.

## Platform and integration limits

The changed helper and join have no platform conditional and use the shared
registered-string lookup. Linux owner1 is executed. Windows, macOS, BSD, SimpleOS,
owner0 and 32-bit paths are source-reviewed only, not executed or cross-compiled.
On 32-bit the stored uint64 length is checked against SIZE_MAX before conversion.
Raw pointer inputs still require readable NUL-terminated storage.

LLVM native join lowering currently coerces its separator to a raw pointer. This
runtime repair preserves a tagged separator when actually received; it does not
prove compiled Simple embedded-NUL separators are retained by that caller.
The MIR fragment-join optimization remains separate unqualified PR3198. Its
actual dependency lowering fails before executable production. Full compiler,
core/MCP native smoke and whole Phase2 tests are blocked by those independent
producer/runner failures, not claimed by this C-owner qualification.
