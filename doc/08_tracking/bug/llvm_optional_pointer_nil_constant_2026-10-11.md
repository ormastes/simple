# LLVM rejects the absent branch of an optional pointer payload

Status: source fix qualified by actual C37 LLVM positive/negative smoke; full generator validation pending.

`if val payload = optional_struct` lowers through ExistsCheck. Its absent branch
intentionally creates `MirConstValue.Int(3)` with the payload result type. For a
struct/map payload, that type is pointer-backed. The word 3 is the runtime nil
sentinel; replacing it with null (0), allocating a new enum, or dropping the
branch would change program behavior.

LLVM `MirToLlvm.translate_const` previously rendered every integer payload as
`add {llvm_ty} value, 0`, yielding illegal `add ptr 3, 0`. This blocked the native
subsystem generator before test discovery, in collection_feedback and
adaptive_text_set. It is not caused by individual test files or memory pressure.

The pointer branch now emits `inttoptr` with the existing target-native integer
width and registers pointer metadata. Ordinary integer constants, MIR lowering,
control flow, evaluation order, option representation, and Cranelift are unchanged.
Cranelift already materializes pointer-backed integer payloads with integer
`iconst`; the supported native AArch64 lane uses the 64-bit word unchanged.

## Regressions and evidence

- `test/unit/compiler/backend/llvm_pointer_integer_constant_spec.spl` directly
  exercises the emitter for SSA-created/registered locals, 32/64-bit targets,
  tagged nil 3, null 0, nonzero/negative bit patterns, and ordinary integers.
  These emitter tests are authored but not executed: the existing compiler-only
  producer cannot run SSpec, and a new full compiler build belongs to its owner.
- `test/fixtures/native_optional_pointer_nil/main.spl` checks absent, present
  two-field payload, absent again, and present payload containing the value 3.
  The unfixed cycle3 producer reproduces the LLVM error with this single source
  module in 12.90 seconds / 481036 KiB maximum RSS. This is a regression
  reproduction, not a post-fix pass. The same fixture builds and runs with
  the unfixed cycle3 Cranelift backend, prints `optional pointer nil: PASS`, and
  exits 0 with all four checks intact. Two initial Cranelift link attempts
  lacked tracked sparse-worktree runtime sources; restoring `src/runtime`
  and counterpart/config roots resolved that setup failure without source edits.
- The original retained generator IR contains five bad constants across two
  modules (two collection_feedback, three adaptive_text_set). Both originals
  fail LLVM verification. Diagnostic copies replacing only those instructions
  with target-width `inttoptr` pass `opt -passes=verify` and `llc -O=2` object
  generation for both entire modules. These copies are diagnostic evidence,
  not a generator binary and not compiler admission.
- Focused 32-bit i386 and 64-bit AArch64 IR bit-roundtrip probes retain exactly
  3, 4097, -1, and 0. LLVM O2 eliminates every conversion, producing constant
  returns with no runtime calls or allocation. Thus the new representation
  introduces no dynamic conversion work in these probes. No broad compiler
  performance or peak-memory improvement is claimed.

Evidence root: `/home/yoon/dev/phase2-six-results-20261011/llvm-pointer-constant-repair`.
Retained input manifests live under the Phase2 generator's
`generator-monitor-final/diagnostics/manifest.json`; changed diagnostic modules,
verification logs, optimized IR and assembly are in `ir-replay/`.

## Actual source-built C37 qualification

C37 debug producer SHA256
`35d0990fb5bc30d3fea07e36d97122b3d2ab4a18b64985b626c54d897d70d666`
contains the source fix. Its immutable runtime capsule was verified before use;
this is a seed-constructed debugging generation, not admitted Stage2 or a phase
promotion. Its source is frozen at `c9cb8d6ac95ab64c95dc74c46772d2c60002271e`.

Using that actual producer (no edited IR), LLVM builds and runs the unchanged
positive fixture: exit 0, `optional pointer nil: PASS`, all four checks intact.
The separate tracked negative fixture changes only expected 37 to 38 (plus its
explanatory comment). It also builds, then exits exactly 2 at that second check,
with no PASS output. Both use fresh producer-bound caches, one worker, CPUs
16–17, no stub fallback and memory monitoring without enforcement.

Positive build: 38.70 seconds, peak process-tree RSS 1387272 KiB.
Negative build: 35.89 seconds, peak process-tree RSS 1387844 KiB.
Both fixture runs take less than the timer's 0.01-second resolution, max RSS
1484 KiB. These are qualification observations, not an isolated performance
comparison against a previous successful LLVM build (the prior producer failed).

Final producer/capsule/source/binary/evidence hash binding:
`llvm-pointer-constant-repair/c37/result.json` under the evidence root above.
The independent Cranelift positive control described above remains passing;
it was not rerun unnecessarily with C37.

Required follow-up: run emitter regressions when the runner works, then rebuild
the actual generator and attach/run its complete test inventories.
No test exclusions or assertion workarounds are part of this fix.
