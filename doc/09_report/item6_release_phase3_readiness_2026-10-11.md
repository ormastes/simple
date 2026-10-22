# Item 6 release_phase3 readiness — 2026-10-11

STATUS: BLOCKED. This report does not admit a Phase 3 runtime or mark Item 6 complete.

## Source and ownership

Integration target: `release_phase3`, revised from `20f619fe31b` to
`9434873b8d3` (PR #3074, cold HIR diagnostic dictionary lookup).
Owned worktree: `C:/dev/simple-item6-phase3-validation-20261011`.
Owned branch: `work/item6-phase3-validation-20261011`.
The existing Item 6 fixes from PR #2860 are already ancestors of this target.
Other sessions' dirty files, processes, outputs and caches were preserved.

## Fixes retained locally

- Normalize the directory returned by Git for Windows through `cd` and `pwd -P`
  before comparing it with the shell's canonical source root. Both readiness and
  recovery authority still reject Git errors and non-root paths.
- Restore `compile_specialized_template`'s declared `text` return by returning
  its computed mangled symbol. Both concrete compiler/linker callers and the
  default/release wrappers require `text`; the previous `Ok(CompiledUnit(...))`
  body violated that signature and fabricated an empty compiled artifact.
- Align readiness assertions with the current diagnostic disclosure, bounded
  diagnostic range filter, and full-`src` source snapshot. Keep the Stage 3
  command/provenance assertions; do not remove them to obtain a green result.

The separate `CompilationContext` trait still declares a
`Result<TemplateCompiledUnit, text>` interface. Its relationship to the concrete
`text` implementations requires runtime verification and is not resolved here.
The specialization helper does not itself implement native code generation.

## Evidence and remaining admission blockers

Windows root fix: shell syntax, whitespace, dirty-root refusal, nested-root
refusal and working/staged environment-boundary guards passed. Smaller-model
and primary review found no P0/P1 in that root fix. These passing checks were
not repeated without changed inputs.

The clean static readiness attempt after that fix refused
`diagnostic-transport-disclosure-missing`, exposing the stale source assertions
addressed above.

An actual bounded invocation of the receipt-matching pure-Simple Stage 2
compiler (`1d18beed32d7156d9dc0ed2025ed6da77af289778f97632b8f57e07e5a7137b8`)
with `check src/compiler/80.driver/pipeline_fn.spl` exited 1 with
`error: unknown command 'check'`. The compiler-only capsule cannot supply the
required compiler/core/MCP/LSP checks. The diagnostic corrected Phase 2 hello
producer is bound to another source revision and is explicitly unqualified.

The provenance verifier still reconstructs an older Stage 3 command: its
Stage 3 argument hash and transcript omit the focused-route marker and
composition selection, and use the old positional entry/cache policy. The
current bootstrap command includes `SIMPLE_BOOTSTRAP_STAGE3=1`, explicit entry,
composition sources and enabled retained frontend/HIR caches. Updating only the
readiness assertion would hide a genuine exact-transcript admission mismatch.

No source-bound Phase 3 PASS or full Item 6 runtime/performance acceptance was
established. Clean/warm/no-op/edit time and RSS evidence, semantic invalidation,
corrupt-cache recovery, equivalent executable behavior and applicable
bootstrap/core/MCP/LSP acceptance remain required by the canonical Item 6 plan.
No new fix was pushed or merged, and no tags/publication were performed.

Local bounded process evidence is retained under
`C:/dev/simple-bootstrap-storage/item6-phase3-validation-20261011/`.

## Bounded continuation: invocation integrity and Stage 2 layout

The next focused defect pass rebased the owned branch onto `3aa33b9f8de`, which
integrates the bounded-bootstrap campaign and shared MSVC environment fixes.

The Stage 3 hash vector omitted `SIMPLE_KEEP_SOURCE_CONTENTS` and
`SIMPLE_MIR_TAG_PROBE`, although the executed command passed both. It also
hashed `--low-memory` without passing that option to the executed Stage 3
command. The producer now uses matching values and options in both paths.

The verifier additionally required every Stage 2 path to contain a historical
`/output/stage2/` transaction component. Current producers write directly to
the manifest output root's `stage2/` directory. It now accepts that exact root
and the previously supported transaction `*/output` donor form, rejects other
roots, and derives admission/transcript/sanity/receiver paths from the selected
Stage 2 output root. Artifact-map identities and exact transcript checks remain.

`stage3-invocation-consistency-test.py` expands the independently written hash
and execution recipes with argument collectors, without running a compiler.
All four Windows/POSIX and low-memory combinations first failed, exposing the
omissions; all four passed after the producer fix. A separate six-case layout
check passed for current roots, legacy donors, and unrelated-root rejection on
Linux and Windows platform suffixes. Already-green cases were not rerun when
the independent layout check was added.

These are orchestration regression checks, not Phase 3 bootstrap acceptance.
The verifier's old full Stage 2/3 argument reconstruction still requires repair,
including independently bound K1/CUDA composition authority. The existing
compiler-only capsule still cannot perform `check`; no exact-source qualified
full CLI was found. The local code is therefore suitable only for a draft PR
targeting `release_phase3`, with no admission, merge or completion claim.

## Focused invocation provenance contract

Full-bootstrap producers now emit provenance v5 with the explicit
`full-bootstrap-focused-v1` invocation contract. Existing descriptor candidate
producers continue to emit v4 and use its unchanged reconstruction path. The
new route is not inferred from arbitrary transcript arguments and is not
accepted through the descriptor-capsule route.

Admission reconstructs both Stage 2 and Stage 3 environment/argument vectors
from singular bound metadata and the established artifact map. It binds K1
policy to its canonical composition, derives CUDA selection from `simple.sdn`,
and verifies the selected template, generated overlay and K1 receipt hashes.
The generated CUDA root must contain exactly its selected source file; extra
modules are rejected. The K1 receipt must identify successful selection and
the same Stage 2/3 transcript and log hashes as the artifact map. Existing
source/runtime/tool snapshots, executable identities, sanity evidence and
exact transcript checks remain required. No artifact-map role is removed.

The focused vector includes retained frontend/HIR caches, compatibility
manifest paths, platform tool environments, explicit entry and compositions,
mission-critical selection and low-memory options. MIR tag diagnostics are
recorded once rather than duplicated through the diagnostic pass-through.
Deploy/handoff/oracle consumers recognize v5 while retaining v4 support.

Eight real-file binding cases passed, covering valid authority, changed K1,
changed generated CUDA, changed compiler manifest, malformed hash, forged
receipt status/transcript and duplicate policy. A subsequent targeted case
passed for an injected sibling module; only the changed closure's valid case
was rechecked. These tests do not establish executable/bootstrap equivalence.

The smaller-model sidecar's independent producer/verifier comparison passed
all six Linux, Windows MSVC and Darwin Stage 2/3 cases, including exact
length-prefixed transcripts. It covers selected low-memory, diagnostic/MIR,
cold-index and mission-critical settings. Darwin Stage 2 initially exceeded
the fixture's 15-second subprocess limit; only that failed case was retried at
45 seconds and passed in 39.9 seconds. Windows Stage 3 was checked after its
diagnostic fixture changed and passed in 33.3 seconds. Other green cases were
retained. Direct diagnostic pass-through compatibility also passed. Primary
review checked the implementation and sidecar assertions; these remain
compiler-free orchestration tests.

A clean, 180-second-bounded static retry-readiness invocation passed at
`51cef235f21`, with source snapshot
`d57812ff9622aef60fca65e68f8dcd88b828cdc339df107ae5aa734045dbf409`.
Its verdict was `static-root-cause-and-route-proven`; it did not run a compiler
or qualify a Phase 3 executable. The branch was then rebased onto
`release_phase3` commit `4c324a98215`. That base update changes CI/review
admission, a release helper, a bug report and Rust-seed LLVM dependency metadata;
it does not change the tested focused command/verifier implementation. The
unchanged green route checks were retained rather than repeated. Full bootstrap
admission must still bind the final source and tool identities.

The Windows handoff self-test rejected missing evidence and tampered executable
content, then failed its symlink case. A separate host probe established that
Git Bash `ln -s` creates a regular copy here (`native_symlink=false`), so that
fixture did not exercise a symlink. Its result remains FAIL, not a platform
acceptance PASS. The deploy guard self-test also cannot select this Windows
host through its Linux/macOS-only platform probe. Neither check was looped.

PR [3098](https://github.com/ormastes/simple/pull/3098) contains the earlier
tested fixes on `release_phase3`; it remains draft. This continuation repairs
orchestration authority and does not claim full Item 6 acceptance. An admitted
full CLI, source-bound Phase 3 bootstrap and the canonical clean/warm/no-op/edit,
semantic invalidation, corruption recovery, behavioral equivalence and
compiler/core/MCP/LSP runtime evidence are still required before landing.

## Located Item 6 migration lane and diagnostic runtime attempt

Revalidation located draft [PR 3072](https://github.com/ormastes/simple/pull/3072),
head `1d874f127a662f8044b44e57aa3f8100fcd86f15`, for the generated-source/index
migration on `release_phase3`. Its worktree and Windows materialization are
preserved. The handoff records a terminal Stage 2 cache-identity refusal before
compiler execution and an explicit three-cycle stop. Its prepared invalidation
launcher was not executed. It also records missing independent generated-plan
selection, enforced producer execution and derived-snapshot consumption.
The current source still rejects generated facets with
`cold-compiled-generated-authority-unavailable`; this is an implementation gap,
not merely a missing test result.

A new isolated diagnostic native build targeted
`src/app/test/package_index_acceptance.spl` using immutable pure-Simple producer
`b580919372e209ea2a10e6d8e919b0f90c5dc3100e76f958f584c5db0ace4778`.
It used this clean worktree's source/runtime, a separate acceptance-entry cache,
two workers and enforced limits. Two controller-envelope refusals occurred
before spawn; the corrected third invocation timed out at 240 seconds, native
status 124. The collector reaped all descendants, reported peak 440008 KiB and
no RSS observer error. No executable or acceptance scenario was produced.
Compiler bytes matched before and after. This stopped cycle was not restarted.
The producer is unqualified and other bootstrap processes were active; no
Phase 3 or performance PASS follows from this diagnostic.

See the [concrete timeout blocker](../08_tracking/bug/item6_acceptance_driver_native_build_timeout_2026-10-11.md)
and external `acceptance-probe/request.json`, `logs/build.log` and
`logs/receipt.env` under the evidence directory above. The acceptance driver
itself explicitly reports owner-only results as incomplete until actual
compiler completion and production filesystem observations exist. Compiling
it successfully would therefore still not close the full 44-scenario contract.
