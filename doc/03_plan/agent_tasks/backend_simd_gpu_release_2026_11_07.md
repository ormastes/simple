# Backend, aspect, SIMD and GPU release reconciliation

Baseline: `origin/release/1.0.0`, `d0c909d681f`, fetched 2026-11-07.

The user authorized parallel fixes and feature implementation, with smaller
workers guided and reviewed by the highest-capability owner. Opus is not
available through this session. At most three workers run beside the root;
five task owners therefore run in waves. This is a work plan, not completion
or release acceptance evidence.

## Shared rules

- Root owns integration and final review. Workers use isolated branches.
- Preserve existing backend request/session, facet catalog and SIMD contracts.
  Any ABI change needs explicit root review before integration.
- A registry selecting built-in passes is not dynamic optimizer code loading.
  A scalar fallback is not evidence of SIMD execution. A source guard is not
  hardware evidence.
- Recheck current source and pending PR diffs before implementation. Do not
  duplicate or merge another author's unfinished fixes.
- New scenario helpers must have real assertions; unavailable evidence stays
  unavailable. No empty or always-passing placeholders.
- Record actual producer, target, source, linked runtime and test count.
  Bootstrap-seed runs do not qualify a self-hosted compiler.
- Follow repository verification requirements. Missing required gates block
  landing; they do not become a PASS through source inspection.

## Five lanes

| Lane | Worker scope | Acceptance boundary |
|---|---|---|
| 1 Backend loading | Reconcile explicit provider loading with host/target policy; implement a confirmed bounded gap | Correct provider admission, builtin compatibility, negative cases and actual provider execution where supported |
| 2 Optimizer loading | Reconcile AST/HIR/MIR optimizer paths and identify the genuine code-loading boundary | Loaded code executes a supported pass with lifetime/ABI validation; built-in routing alone never closes this lane |
| 3 Aspects | Reconcile packaging, catalog acquisition and frontend routes; implement a bounded integration gap | Existing catalog/SMF contracts preserved; truthful automatic packaging status and executable integration evidence |
| 4 CPU/SIMD | Verify current native dispatch and compiled-kernel admission | Supported native kernel execution and scalar parity; unavailable implementations rejected without rejecting valid lower-ISA vector fallbacks |
| 5 GPU | Review CUDA/Vulkan codegen/loading and pending fixes | Typed unsupported-operation failures, validated target artifacts and applicable real device receipts; platform gaps explicit |

Each lane follows: current-state/PR inventory -> concrete file boundary and
plan -> root guidance -> implementation plus focused regressions -> review ->
required verification -> landing. A failed verification returns to its owner;
repository iteration limits apply.

## Pending PR inventory

The GitHub connector's issue search returned issues despite PR qualifiers;
`gh pr list` supplied the open-PR inventory instead.

- #7316, dynamic GPU dimensions: actual diff replaces a recoverable error and
  warning with `error_fatal` and the expression span. Draft; self-hosted
  execution and compiler/core/MCP checks explicitly unrun. Do not duplicate.
- #7465, LLVM call ABI ownership/GEP widths: related backend correctness, not
  evidence that architecture-based dynamic provider selection is complete.
  It merged during this investigation as `75e6c978808`; it must not be
  duplicated or described as still pending in the final handoff.
- #7459, MIR/Cranelift review follow-ups; #7441, function alignment; #7256,
  narrow signed negation: inspect before changing overlapping backend owners.
- #7294, advice dependency roots, stacked on #7292 parser state ownership:
  inspect before altering aspect/frontend dependency routes. Its fixed native
  attempt segfaulted before assertions and the six-attempt budget is exhausted;
  this work must not retry that lane or claim it accepted.
- Merged #7261 (`8395b84790f`) moves text SIMD to per-level provider DLLs with
  pin/ABI checks. It does not claim full deploy qualification or all-platform
  acceptance. Merged #5810 repairs dynload `Both` output staging; do not
  resurrect that older defect as new work.

## Current evidence and limits

The Windows `bin/simple.exe --version` identifies itself as a Rust bootstrap
seed. No qualified self-hosted runtime has been established for this work.
Native C tests may establish their own runtime-owner behavior but cannot stand
in for required Simple compiler and integration checks.

The old audit's Engine2D SIMD gap needs correction: current source already
connects `create_cpu_simd` to native pixel routines. Lane 4 must establish a
specific current defect before changing that path. Nothing in this plan marks
all five features or their tracked bugs complete.

## CUDA provider check on this baseline

`scripts/check/check-cuda-bitmap-provider-v1.shs` ran once through WSL Ubuntu,
using current C runtime/provider source and the real CUDA device. Exit 0:

- mocked driver lifecycle/failure policy passed (not hardware evidence);
- bad digest rejection passed with driver unloaded;
- authenticated device execution passed: eight launches, 1,506 words,
  thread and caller contexts, 128 canaries, copied input;
- `image_authority=none`: no image-rendering authority is claimed.

The tool captured the result stdout and exit status. A subsequent copy from
the WSL `/tmp` output directory failed because that directory was absent;
source/artifact hashes, compiler identity and watchdog receipt were therefore
not retained in the Windows workspace. This is observed provider execution,
not a retained provenance-bound qualification receipt. The already-passing
check was not rerun. No Vulkan, generated-MIR kernel, AST/HIR/MIR optimizer,
self-hosted compiler or cross-platform acceptance follows from this result.

## Implementation receipts before final review

- Backend staging: use the existing checked `secure_temp_dir` Result wrapper,
  whose implementation rejects both empty and NIL text, and skip cleanup for
  absent staging paths. Existing content-identity behavior specs remain the
  oracle; a proposed source-string test was dropped because it merely mirrored
  the implementation. The worker's seed attempt could not resolve `std.spec`
  and executed no examples. No dynamic backend policy completion is claimed.
- CLI aspect admission: reject oversized files before reading, noncanonical
  pack flags, and malformed directory/frame geometry before registration.
  New cases require malformed admission to fail without publishing the path,
  then admit corrected bytes through the same loader. The worker's seed
  attempt failed parsing `windows_redirected_process.spl` before examples ran.
  Automatic aspect packaging and frontend facet syntax remain open.
- Optimizer loading: no bounded replacement of `PassKind` routing can supply
  a native optimizer DSO. The native ABI direction requested by the user needs
  a versioned pass entrypoint and ownership/lifetime/failure rules. Existing
  backend-provider lifetime/boxed-byte transport patterns can be reused, but
  its final-native-object result is not transformed MIR. Establish a complete
  MIR round-trip schema and validated typed decoder, then exercise an identity
  pass from an actual loaded library with malformed-output and lease-lifetime
  tests before wiring manifest execution. AST/HIR need their own corresponding
  contracts. No dynamic optimizer loader PR was identified in this inventory.
- GPU lane: no additional code change selected. Vulkan mapper layout helpers
  have an apparent std430 discrepancy, but the worker found no production
  consumers; changing an inactive helper does not establish a real GPU
  execution feature. #7316 remains the pending dynamic-dimension diagnostic
  fix. Existing CUDA/Vulkan implementation and incomplete device/platform
  qualification must remain separate claims.
- Engine2D SIMD: compile existing SSE2 helpers independently of AVX2 support
  and route baseline-only x86 builds through them. The explicit
  `SIMPLE_RUNTIME_DISABLE_AVX2` build switch models a build without AVX2 code;
  the older force flag continues to model runtime feature selection. MinGW
  native span validation with AVX2 code disabled passed, including parity and
  a SIMD hit assertion. clang-cl compilation is blocked by missing Windows SDK
  headers (`string.h`), so no clang-cl runtime qualification is claimed.
  The separate sliced-helper gate failed with 1,537 blend mismatches. Review
  found a source-level contract disagreement: its reference forces opaque
  alpha while the production/span contract preserves straight-alpha output.
  This is not a passing gate and does not establish a baseline execution
  result. No broad SIMD correctness/performance or per-level provider migration
  completion follows from the focused native span result.

Required Simple compiler/core/MCP checks and generated-manual validation have
not passed with a qualified runtime. Source review and native runtime-owner
checks must not be promoted into a repository-wide verify PASS. Unqualified
implementation stays on review branches; this plan does not authorize a
verification exemption or claim all bugs/features complete.

## Independent highest-capability review

An independent `gpt-6-astra` reviewer inspected the exact backend/aspect diff
and final five staged SIMD files. Verdict: **source-approved for draft only**;
no confirmed introduced P0/P1/P2 source defects. Verification and landing are
**blocked**, not approved. In particular, the failed helper gate and missing
qualified Simple/manual checks remain open. CUDA stdout is not a substitute
for the missing provenance receipts. The review does not approve merging
unqualified source into the release branch.

## Subsequent user-directed scoped landing

After the draft and its verification limits were reported, the user explicitly
requested landing these fixes and improvements after review. The earlier
draft-only disposition above is retained as the historical review outcome;
this subsequent decision supersedes its publication restriction for the three
scoped source fixes, without claiming verification PASS or complete features.

The independent highest-capability reviewer checked integration head
`897460ab097` after merging release `8e63eca53d5`: all eight code/test blobs
match the previously reviewed source, the release-relative diff contains only
the intended nine paths, and the bug database and seals match current release.
No introduced P0/P1/P2 source defect was found. Recommendation: normal PR
landing conditional on required CI passing. No failing-check bypass or admin
merge is authorized by this decision. Qualified runtime/manual checks,
clang-cl qualification, and the helper-oracle discrepancy remain pending;
backend policy, actual optimizer DSO loading, and automatic aspect packaging
are not completed by landing this scoped change.
