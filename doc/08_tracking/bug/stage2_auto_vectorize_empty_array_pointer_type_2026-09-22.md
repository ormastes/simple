# Stage2 auto-vectorization loses the conditional block-array element type

Date: 2026-09-22. Base: `2b4014f3e9cb9245f43e147e8b4b6d8d042300b9`.
Status: focused native regression PASS; independent Astra review PASS; rebuilt
Stage2 admission pending.

## Cause and correction

After 899 modules compiled, Stage2 positional hello-world admission exited
139. Crash `simple-2026-09-22-223042.ips` identifies
`compiler__mir_opt__mir_opt___AutoVectorize__recipe__mir_pattern_match_elementwise_loop+104`
(image offset 7294204). The rejected candidate SHA-256 is
`7ce475b90f1ee388ec4d8be829f450dea5fc223ab39d9fab6989b4e7c5383084`;
the parent preserved it and the crash report under
`build/evidence/macos-enforced-bd544/stage2-lexer-cleanup-2b4014f`.

`run_auto_vectorize` inferred `blocks_to_scan` from
`if cur_func.simd_disabled: [] else: cur_func.blocks`. The frozen bootstrap
producer's `hir/lower/expr/control.rs::lower_if` takes the then-arm type;
`expr/collections.rs::lower_array` assigns an empty array its configured
default element type. The caller's disassembly confirms integer treatment:
`rt_index_get`, `rt_value_unbox_int`, then `sxtw` truncate the `MirBlock` value
before calling the matcher. The matcher then reads the invalid block pointer.

Declare `blocks_to_scan: [MirBlock]`. This preserves both conditional arms,
SIMD refusal semantics and existing traversal; no allocation, loop, copy or
runtime check is added. Green disassembly passes the full `rt_index_get`
result to the matcher without integer unboxing or sign extension.
An exact-lane search of `_AutoVectorize/` and `auto_vectorize*.spl` found no
other untyped empty-first conditional array binding.

General empty-collection conditional inference remains a compiler follow-up:
an unannotated `if disabled: [] else: typed_struct_array` should unify element
types or diagnose a mismatch, never infer integer iteration over structures.
The preceding malformed HIR type diagnostics are separately unresolved; this
fix does not establish their cause or eliminate them.

## Native regression

Worktree: `/Users/ormastes/simple-tmp/stage2-hir-sigsegv-20260922`.
Evidence: `build/native_probe/auto_vectorize_block_array/`.
Fixture: `test/fixtures/native/auto_vectorize_block_array.spl`.

The fixture imports the real pass and constructs two real `MirBlock` values
with IDs 41/73 and labels `first`/`second`. It checks typed conditional
selection with dynamic disabled/enabled parameters (length 0/2, ID sum 0/114),
then runs the actual pass and checks function name, retained count, both IDs,
both labels, and `simd_disabled`. These non-loop blocks must remain unchanged.
The disabled-only process exercises refusal; the default process also enters
the matcher through the enabled path.

Red disabled-only passed, while red default reproduced exit 139, as recorded
in the original execution capture and fixer handoff. The retained red log
reports abnormal termination but does not itself contain the numeric exit.
Green
disabled-only and default each ran once and exited 0 with exactly
`auto-vectorize-block-array-pass`. Both green executions used the existing
process-tree guard with a 20-second bound and 5,859,375 KiB cap; both receipts
record `observer_errors=0` and `quiescent=1`. Sampled process-tree peaks can miss
these very short runs; the table uses `/usr/bin/time -l` maximum RSS for runs.

| Measurement | Red | Green |
|---|---:|---:|
| Disabled-only run maximum RSS | 9,093,120 bytes | 9,125,888 bytes |
| Disabled-only run elapsed | 0.34 s | 0.34 s |
| Default run | 139 | 0, 0.00 s, 9,093,120 bytes |
| Successful build elapsed | 5.65 s | 5.13 s |
| Successful build sampled tree peak RSS | 239,408 KiB | 271,056 KiB |
| Successful build compiled / cached / failed | 1 / 64 / 0 | 2 / 63 / 0 |

The different incremental rebuild counts limit build-time comparisons. The
32 KiB disabled-run RSS difference and coarse timings do not establish a
statistically significant regression or speedup. Both builds remain under
the ordinary 1 GB target and enforced cap, with zero observer errors and
quiescent completion. The annotation adds no runtime work.

Initial `red-build.log` records a fixture construction error (`Return` instead
of MIR's `Ret`); the corrected fixture's successful baseline is retained in
`red-fixed-fixture-build.log`. No production change preceded the red crash.

Native binary SHA-256:

- Red: `be93b8daee0a88e8cac26c5f28bcdb62906342bd306e6be9390b412d48552bc3`.
- Green: `d54aef9ae36e5f023661ef81791552ca77a459cc81597d69f7a5bfca440be015`.
- Frozen producer: `3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.

Source SHA-256:

- Base rewrite: `8263ca67daa69d1a2424ba5192257f253b9b732fe2b0072b0538a4601cb807dd`.
- Fixed rewrite: `554d80e7df9d000cc2b67b936f7583c9969e0c026f318ce83696b56ce5c5a8d6`.
- Fixture: `a8f3b029308a0f132922b165bb19ce024512d08b6d8f094054a32479e8fdfa05`.

Reproduction uses the parent lane's frozen `stage2-runtime-authority/simple`
with `SIMPLE_NATIVE_BUILD_RUST=1`, `SIMPLE_BOOTSTRAP=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, and
`SIMPLE_LIB="$PWD/src"`. Compile with `native-build --backend cranelift
--runtime-bundle core-c-bootstrap --runtime-path <authority> --source
src/compiler --source src/lib --entry-closure --threads 2 --cache-dir
build/native_probe/auto_vectorize_block_array/cache --mode one-binary --entry
test/fixtures/native/auto_vectorize_block_array.spl --output <red-or-green>`.
Builds use the existing RSS watchdog with a 180-second bound. Run normally
and with `SIMPLE_VECTOR_PROBE_DISABLED_ONLY=1`. Cache is preserved.

Independent Astra review found no blockers in the annotation, fixture,
disassembly or resource evidence. Coverage is limited to non-loop block
traversal; actual vectorization correctness and general conditional inference
remain outside this scoped approval. The working/staged direct-env guards,
whitespace check and executable-spec layout gate are commit checks, separate
from compiler admission.

This is bootstrap-only focused verification using the frozen authority, not
production self-hosted verification. The worktree has no admitted release
runtime. Full compiler/library/MCP checks and rebuilt Stage2 admission remain
with the parent lane. No full bootstrap, deployment or push was performed.
