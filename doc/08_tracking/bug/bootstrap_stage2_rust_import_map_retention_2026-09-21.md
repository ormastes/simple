# Stage2 Rust import-map retention and import resolution churn

Status: OPEN. Diagnostic evidence only; no product fix or memory-budget pass.
Scope: macOS aarch64, source `d3d58077823`, canonical Stage2 producer, jobs=8.

## Evidence

The saved Stage2 command transcript selects the Rust bootstrap authority with
`SIMPLE_NATIVE_BUILD_RUST=1`. Its build completed 898 modules in 750.9 seconds
plus 13.0 seconds linking. The reported full-run peak is 2,786,033,664 bytes.
Every saved progress sample contains zero processes/RSS, so that peak cannot
be assigned to an exact phase or subprocess from the original evidence.

Two fresh-cache native-build probes reused the producer and original arguments,
changing only private output/cache/HOME/TMPDIR paths and diagnostic settings.
They were terminated after 55.457 and 35.833 seconds; no bootstrap was rerun.
The [retained memory profile](../../09_report/compiler/evidence/stage2_rust_import_memory_2026-09-21/profile.json)
includes producer identity, RSS series, stack excerpts, vmmap summaries, and
the raw allocator-counter snapshot.

| Observation | First probe | Counter probe |
|---|---:|---:|
| Reachable discovery | 1.783 s | 1.607 s |
| Import-map construction | 3.408 s | 3.408 s |
| RSS near 15 s | 901,600 KiB | 903,328 KiB |
| Maximum sampled RSS | 1,872,080 KiB | 1,343,360 KiB |

At 15 seconds the sole compilation worker was resolving the export-heavy
`__init__.spl`: `build_use_map_from_ast` → `collect_use_imports` →
`resolve_import_name_strict` → `mangled_matches_use_path`. All eight Rayon
workers were waiting. The first cached object appeared near 19 seconds;
subsequent RSS growth overlaps parallel compilation. The 55-second maximum
must **not** be attributed entirely to the earlier single-worker phase.

At 20.416 seconds, RSS was 1,137,184 KiB. A subsequent LLDB snapshot read
80,333,502 live Rust bytes, an 813,124,472-byte live high-water mark, and
13,379,207,128 cumulative requested bytes over 181,062,275 allocations.
This demonstrates severe allocation churn and a large gap between resident
memory and live Rust objects. Rust counters exclude C/LLVM allocations.
The vmmap profiles additionally distinguish system malloc and tagged mappings;
mapping names alone do not prove ownership.

## Cause and scope

`native_project/imports.rs:353` retains every parsed module AST together during
import-map construction. Later, each single import scans global raw names;
candidate checks repeatedly allocate joined prefixes, normalized strings,
split vectors, and match vectors (`imports.rs:1143`, `:1234`, `:1325`).
These are concrete frontend peak/churn sources; their exact shares of the
original 2.786 GB maximum remain unmeasured.

The pure-Simple counterpart resolves indexed `ModuleSurface` owners in
`module_import_resolution.spl:305` and `module_surface_registry_index.spl:143`.
It has no corresponding global mangled-name normalization/split loop.
No speculative change was made to pure-Simple code; Rust edits were outside
this task's permitted scope.

Future seed work should bound simultaneous AST retention and avoid per-candidate
normalization allocations while preserving import precedence and ambiguity.
Any fix requires executable import correctness coverage, scaling assertions,
and before/after memory profiles. These stopped diagnostic probes satisfy none
of those acceptance gates and do not establish Stage3 memory compliance.
