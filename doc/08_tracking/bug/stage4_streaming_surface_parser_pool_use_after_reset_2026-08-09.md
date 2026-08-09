# Stage4 streaming surface phase handoff SIGSEGV

## Status

Open, release-blocking for the Stage4 full CLI closure.

## Reproducer

Use the admitted pure-Simple Stage3 host and run the one-binary CLI entry
closure with `SIMPLE_STAGE4_STREAMING_SURFACES=1`, low-memory mode, phase
profiling, and `SIMPLE_NO_STUB_FALLBACK=1`.

The x86_64 Linux run parses and promotes all 1,351 unique module surfaces, then
terminates with SIGSEGV (`exit 139`) before the first phase-3 HIR progress row.
The earlier entry-alias and missing `app.cli.main` failures do not recur.

## Evidence

- Pure-Simple Stage2 and Stage3 recovery both passed compiler sanity and native
  build capability checks.
- Stage3 provenance SHA-256 after the final recovery:
  `54e44eed5c9972bb027eca5feff65e947e61d20e1d53ac3961f93756ea3827ef`.
- Three capped Stage4 verify/fix cycles ended at the same boundary after
  `phase2:surface:file:released ... seq=1351` with exit 139.
- Replacing `Option<ModuleSurfacesByName>` first with direct context containers
  and then with a class-backed builder did not move the failure boundary.

## Disproven root-cause direction

The first review suspected shallow parser-pool retention. Runtime inspection
disproves the premise that promotion protects only the outer value:
`rt_transient_heap_promote` recursively traverses arrays, dictionaries, enums,
closures, and raw aggregate words, clears each matching transient scope id, and
has a C self-check covering nested aggregate, dictionary, enum, and closure
survival. A detached DTO refactor is not justified without evidence that a
specific parser edge is invisible to that recursive classifier.

Replacing `Option<ModuleSurfacesByName>` with direct context containers and
then a class-backed builder did not move the crash boundary. The next run must
use statement-level phase markers to distinguish final-loop exit, context copy,
builder handoff, tuple return, and orchestration context installation.

## Required fix

1. Capture the last reached statement-level phase marker after surface 1,351.
2. Fix the exact failing ABI/ownership operation rather than changing transport
   shape speculatively.
3. Keep per-source `ast_reset()` and transient-scope reclamation.
4. Add a focused regression for the identified handoff operation.
5. Rerun the full 1,351-surface Stage4 closure once. Acceptance requires phase-3
   progress, a linked executable, sanity smoke, and no stub fallback.

## Platform impact

x86 Stage4, ARM/macOS native bootstrap certification, and SimpleOS/FreeBSD QEMU
handoff remain unproven until the full CLI Stage4 artifact exists.

## 2026-08-09 resolution evidence

The parser-to-HIR crash was caused by incomplete transient ownership promotion. `ModuleSurfaceBuilder.add_parsed` mutates `surfaces`, `index_by_name`, and `index_by_path` inside the transient parser scope; promoting only the newest `ModuleSurface` left those owning containers reclaimable. Promoting all three containers before scope teardown moved the profiled Stage4 build through complete HIR typecheck into phase 4. The remaining synthetic `nilnil` monomorphization diagnostic is a separate preprocessor assembly defect and is tracked by the Stage4 plan checkpoint.
