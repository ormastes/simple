# Stage 4 AST/HIR memory audit — 2026-09-22

STATUS: WARN — runtime ownership controls pass; compiler admission remains blocked.

The [AST/HIR overlap bug](../08_tracking/bug/bootstrap_stage4_ast_hir_overlap_memory_2026-07-27.md)
remains open. This audit adds evidence and identifies existing repair owners;
it does not add a second implementation of their changes.

## Source and overlap audit

Baseline: `e0dd873da1b7828389db4eb60e82972cc8245313` (`origin/main`).
Isolated worktree: `D:/wk-p1-stage4-ast-hir-memory`.

The baseline already reparses one module inside a transient scope, keeps the
scope active through HIR lowering, promotes retained HIR/diagnostics/flat HIR
and frontend registries, then reclaims parser storage. The original report's
proposed streaming architecture therefore exists. Its full compiler acceptance
criteria still require execution evidence.

| Existing PR | Scope relevant to this bug | Evidence boundary |
|---|---|---|
| [#1282](https://github.com/ormastes/simple/pull/1282), `9ef8fd5caf86d2969f7779d529c2165e18b7a745` | Adds phase-wide memo/index promotion to **both** streaming and retained-parser HIR paths; scopes retained-parser lowering scratch and resets module-local enum owner rows. | Open draft. Its published verification uses seed tests and lacks native ownership/RSS proof. Do not duplicate its lifetime repair or assume it is admitted. |
| [#1203](https://github.com/ormastes/simple/pull/1203), `384c9c74cbfef5eb713f03dd90203076c4edf427` | Compacts retired allocation-registry slots without growing tables when live allocation demand is bounded, in native and composed-memory runtime owners. | Open draft. Published C fixtures cover registry churn; this does not establish the cause or resolution of whole-compiler HIR memory growth. |
| [#1281](https://github.com/ormastes/simple/pull/1281), `e75d3412723c5a1806ded3a9251cf4afa3701e62` | Caches SSA liveness metadata in seed object emission. | Separate downstream optimization. Its seed scaling receipt has no RSS measurement and is not AST/HIR ownership evidence. |

The PR information above is an audit of the cited revisions and their published
receipts. None of those patches was applied to this baseline worktree.

## Bounded checks executed

1. The installed Windows executable's `--version` explicitly reported that it
   is a Rust bootstrap seed. Path:
   `C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe`.
   SHA-256: `6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`.
2. The existing multifile Stage 4 gate was invoked with four files, four
   functions per file and a 30-second outer timeout. It stopped before
   compilation with `error=invalid_stage4_candidate_provenance` for the
   executable's absent `.provenance.env`. This is a prerequisite failure,
   not a compiler memory reproduction or a passing RSS check.
3. The baseline core-C runtime capsule completed its 65 checks on WSL Ubuntu
   22.04, Linux x86_64, using the wrapper's default `/usr/bin/cc` (GCC 11.4.0).
   Both transient heap ownership and thread-affinity selfchecks report
   `SELFCHECK PASSED (0 failures)`. This is GCC runtime evidence, not Clang
   host-policy, Windows codegen, or self-hosted compiler admission evidence.

The first capsule invocation failed before tests because WSL Git could not
resolve the Windows worktree metadata path. The successful invocation mapped
`GIT_DIR`, `GIT_COMMON_DIR`, and `GIT_WORK_TREE` to their `/mnt/c` and `/mnt/d`
locations. No passing check was rerun.

The exact runtime-owner controls include unreachable graph reclamation,
retained cyclic/raw aggregate graph promotion, promoted raw sibling survival,
follow-up scope reuse, string alias ownership, and registry return to a fixed
bound across 128 rounds of 256 transient strings. Adjacent controls cover
100,000 persistent strings, 20,000 persistent arrays, and thread affinity.
These checks support bounded live-object retention for their fixtures; they
are not a general leak-detector run or a whole-compiler retention measurement.

## Timing and memory limits

| Workload | Wall time | Recorded RSS | Interpretation |
|---|---:|---:|---|
| Build current baseline core-C runtime capsule and run its checks | 87.56 s | 144,624 KiB | GNU `time -v` maximum RSS for the command and waited children; **not** simultaneous aggregate process-tree RSS and not the standalone ownership fixture's RSS. |
| Four-file Stage 4 compiler gate | Unavailable | Unavailable | Candidate provenance rejected before compilation. |
| Patched compiler versus baseline | Unavailable | Unavailable | No admitted source-matched self-hosted compiler was available for either side. |

There is no claimed speedup, RSS reduction, process-tree peak, or compiler leak
clearance. The native Windows compiler path, Clang runtime build, macOS,
FreeBSD, ARM64, other CPU targets, LLVM/Cranelift and GPU/VHDL backends were
not executed. Source-level HIR ownership changes are shared by native targets,
but that does not prove generated-code or runtime-provider parity.

## Remaining admission work

The following are prospective comparison budgets, not measured results or a
claim that the existing wrappers enforce relative budgets. Apply them to the
same fixture/host/toolchain in separate baseline and repaired processes:

| Repair goal | Required improvement | Bound in the other direction |
|---|---|---|
| Memory/lifetime repair | On the 40-file fixture, repaired sampled process-tree RSS must be at most 95% of baseline, and at most 409,600 KiB. | Repaired wall time must be at most `1.10 * baseline_seconds + 1` and at most 120 seconds. |
| Performance repair | Repaired wall time must be at most 95% of baseline and at most 120 seconds. | Repaired sampled process-tree RSS must be at most `1.05 * baseline_KiB + 16384`, and at most 409,600 KiB. |
| Both directions | All semantic/ownership controls pass; four-file and 40-file cases complete. | Zero lost/unreachable allocations in a leak-checkable fixture, zero invalid accesses, and zero surviving workload descendants before sampler cleanup. Any unmeasured condition remains BLOCKED. |

For the retained-HIR probe from #1282, additionally retain its two-module and
16-module results separately; each must meet its existing 120-second and
1,048,576-KiB absolute bounds. Those wrapper numbers are per-process GNU-time
RSS; collect the additional sampled process-tree RSS before making a relative
memory claim. Do not infer leak freedom from RSS alone. Full Stage 4 on the
original 4-GiB host additionally requires sampled process-tree RSS below
4,194,304 KiB without OOM; this bounded audit sets no full-bootstrap time claim.

The [reproduction recipe](evidence/stage4_ast_hir_memory_2026-09-22/reproduction.md)
names the exact gates, executed commands, candidate/source hashes, and
prospective process-tree sampler invocation. The sampler uses 10-ms snapshots;
its result is a sampled peak, with possible shorter-lived peaks explicitly
unobserved. Windows requires a Windows-capable tree sampler before equivalent
admission; the Linux helper cannot supply that evidence.

Use a source-matched admitted Stage 3 candidate with its provenance receipt.
Run the existing bounded multifile gate and retained-HIR probe on baseline and
the integrated repair, recording wall time and simultaneous process-tree peak
RSS in separate processes. Check semantic output and retained-root survival,
then run the full Stage 4/4b/5 acceptance sequence on the target host. Retain
the original bug's open status until those checks pass; no diagnostics or
stub-fallback gates may be disabled to obtain a binary.

## Retained receipts

[Evidence directory](evidence/stage4_ast_hir_memory_2026-09-22/): runtime
capsule manifest, runtime ownership/thread-affinity output, build timing,
capsule result, and rejected compiler-gate output. The manifest records source
and tool hashes; build products remain in the local audit worktree.
