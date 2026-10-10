# CUDA policy audit across the seven host plans

Source baseline: release `f92764f2b97`; release subsequently advanced by a
documentation-only change to `5646a90e73e`. Status: **WARN / partial; do not merge
as fully verified**. User selected static/dynamic/disabled CUDA on 2026-10-10.

The seven items are the distinct plans in
[the host completion matrix](../../seven_plans_host_completion_2026-09-29.md),
not seven invented CUDA mechanisms.

| Item | CUDA relationship and finding |
|---|---|
| 1 Platform/parser/dynload/release | Compiler PTX emission and runtime CUDA device availability are distinct. Compiler dynamic artifact admission and host lifecycle tests remain open. |
| 2 SCV/jj/GitHub textual databases | No direct compiler CUDA provider route found. SCV cold source admission delayed the disabled full-build probe; this is not evidence of CUDA support. |
| 3 Typed DataFrame/query optimizer | Any future GPU physical-plan selection must consult admitted capability and preserve reference semantics; this patch makes no claim of GPU lowering completion. |
| 4 mold/MDSOC++ linker | PTX is a GPU artifact, not a native object; CUDA dynamic requests must not use ObjectEmit/finalize_object. Linked disabled-symbol exclusion remains open. |
| 5 Kernel/extension aspects and size | Selected source overlays replace unconditional CUDA registry composition. Runtime #2840 and aspect packs are separate contracts. Full disabled closure and size proof remain open. |
| 6 Compile optimization | Manifest plus selected-template identities distinguish enablement/placement at source/cache admission. Dynamic provider/ABI/artifact identity remains future work. |
| 7 Profile-switchable containers | Profiles must not imply device capability from PTX emission or choose unavailable GPU execution. No direct compiler-provider implementation found in this plan. |

## Existing other-agent work

Original workspace dirty files were read only. Its registry diff replaces the
native-safe character comparator with text `<`, reintroducing a documented
bootstrap ordering hazard; its PTX edit drops local type annotations. Neither
change disables CUDA. Those unrelated changes were not copied.

Open draft PR #2840 (`work/item5-cuda-registry-release-20261010`) changes native
runtime provider symbols/twins/dynload and LLVM bitcast lowering. It does not
implement the compiler GPU-output capability or its provider lease.

## Changes

See [composition architecture](../../../04_architecture/compiler/cuda_backend_composition_policy.md).
The CUDA port is separate, target truthful, and preserves options. Static remains
the committed manifest default. Disabled and dynamic templates do not import
the implementation. Driver checks reject unselected/disabled/dynamic CUDA before
cache success and prevent explicit provider requests from silently using static.
Unified emission uses the selected registry and retains other output legs.

## Executed evidence

- Native policy probe: **PASS**, exit 0, `CUDA_PLUGIN_REQUEST_PASS`, 13 rejection,
  provider-independence and install-lifecycle assertions. Producer:
  `/home/yoon/dev/simple-named-variant-pattern-20261010/build/native_probe/explicit-call-types/simple-next`,
  SHA256 `538148aecd19edb2cd0cf4ea2d85f01f82cc71622d765eded7ac83a5bb765afc`.
  One worker, one-binary, `SIMPLE_NO_STUB_FALLBACK=1`; no seed fallback.
- Production manifest selector extracted and exercised: **PASS**, eight mode/error
  cases plus independent disabled-placement cache identity. Output directory
  containing spaces worked. `auto` is explicitly rejected, not mapped to static.
- Bootstrap shell syntax and working direct-env guard: **PASS**.
- Initial full driver-helper native fixture: **BLOCKED** by existing MIR errors
  for BackendCapability/BackendRole equality and receipt Result err/unwrap.
- Disabled full-bootstrap attempt: bounded to 45 seconds; see local retained log
  `build/cuda-policy/disabled-closure-build.log`. No native closure or symbol
  exclusion certification follows from absence of output during cold admission.

Local logs are under `build/cuda-policy/` in the isolated CUDA-policy worktree.
Unit/system specs are updated but not executed by the diagnostic-only compiler.
The focused policy probe does not prove static PTX emission or dynamic loading.

## Remaining acceptance

Run real MIR kernel PTX emission, verify both compiler CUDA implementations and
PTX builder absent from disabled source closure and symbols, check cache/provider
identity gates, implement/version/admit GPU artifact output and lifecycle,
execute required compiler/lib/MCP/LSP and smoke gates, then review the exact
integrated commit. Host certification cells remain unchanged.

## Actual disabled-closure failure and source precedence correction

A second attempt used combined pure-Simple producer SHA256
`67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`.
Its actual phase-1 closure contained 1,169 sources and bound the default
`src/plugins/backend_registry/selected_cuda_backend.spl` despite the leading
disabled source root. Consequently CUDA backend, port, mapper and PTX builder
were present. This is a **FAIL**, not disabled certification. The bounded full
build retained its log at `build/cuda-policy/disabled-combined-build.log`.

`driver_source_pipeline_loading` probed the canonical checkout before explicit
roots. Its fallback also used the checkout-first resolver. The correction adds
an explicit-root resolver that honors source order, numbered directories,
std/lib aliases, and named-import suffixes before canonical fallback. Relative
imports remain importer-owned. Numbered-directory ambiguity remains rejected.
CUDA/K1 precedence, ordinary resolution, ambiguity, relative paths and suffixes
have regression specs; they have not yet run against a rebuilt producer.

A separate source audit mirroring native_build_closure (including generated
barrel-origin comments, sibling modules, lazy imports and source-root order)
found disabled/dynamic 1,127 nodes with zero CUDA implementation paths and static
1,133 nodes with four CUDA implementation paths. It recorded 693 unresolved
imports for disabled/dynamic, zero CUDA/PTX-related; therefore this audit is
limited evidence, not a substitute for the failed actual phase-1 receipt.
The legacy backend/__init__ barrel was not reached; its optional exports were
left intact rather than breaking public API without a demonstrated path.
Root order already participates in native_build_closure's `_nb_scv_key_v1` via
`source_dirs.join("|")`; manifest and template digests appear in generated root
identity. A rebuilt producer and final linked-symbol audit remain required.

## Review correction: ambiguity is not absence

Root review found an introduced authority bug in initial commit `11fdfa806e7`:
ambiguous numbered overlays returned empty text, allowing a later valid source
root or checkout fallback. The tri-state correction preserves `Found`, `Missing`
and `Ambiguous` across selected-root traversal and pipeline fallback. Explicit
CUDA/K1 ambiguous overlays with valid default roots, exact-root precedence,
normal missing fallback and relative behavior have executable regression specs.
The native owner probe includes a forbidden fallback that asserts false if it
is invoked for either `Found` or `Ambiguous`.

The first bounded native owner attempt failed at MIR enum construction
`SourceRootResolutionV1.Found`: payload type mismatch at index 0. An explicit
`text` binding for the typed fallback callback result and retaining existing
terminal variants were applied; this compiler-inference limitation is recorded
here rather than treating a source-only test as executable evidence. Broad
filesystem and integrated closure qualification remain pending.

The corrected owner compiled to a two-object native executable, but exited 7
after six successful assertions. The final diagnostic build also exited 7,
printing `second-match=AMBIGUOUS:196341791234865` instead of the expected path.
This is **FAIL**, not twelve passing assertions. The compiler/payload-formatting
failure is recorded in
`doc/08_tracking/bug/source_root_resolution_native_enum_failure_2026-10-11.md`.
Three bounded attempts are exhausted; the source correction and executable
regressions are reviewable, but filesystem specs, native owner admission and
integrated disabled closure/symbol gates remain pending. No full rebuild ran.
