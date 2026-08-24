# Stage 3 self-host SIGSEGV while lowering `values_equal` after full HIR

**Date:** 2026-08-25  
**Status:** SECOND FIX IMPLEMENTED — rebuilt-compiler evidence pending
**Platform:** `x86_64-unknown-linux-gnu`, LLVM backend, dynload runtime

## Reproduction

The fresh trust-root run used an isolated jj workspace and a newly rebuilt Rust
seed/runtime. Stage 2 passed compiler sanity plus struct receiver/runtime
capability and was admitted. Stage 3 was then resumed from that immutable
artifact:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted=build/bootstrap-gpu-r3 --jobs=1 \
  --bootstrap-receipt=build/bootstrap-gpu-r3/planner-admission-stage3.env
```

The wrapper exited 139 (`Segmentation fault (core dumped)`). Evidence is in
`build/bootstrap-gpu-r3/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## Established boundary

- Parse/HIR completed for all **693/693** modules.
- HIR finalization completed **948/948** and post-HIR validation completed
  **693/693**.
- The earlier fabricated `unresolved name: __p-1` diagnostic did not recur.
- MIR lowering reached `src/compiler/backend/backend/interpreter.spl`.
- The last function marker is `lower_function:body-start values_equal`; the
  final expression marker is `block:stmt 0`.
- Immediately beforehand, `resolve_sym_name` completed, but its body emitted
  `WARNING: unresolved method call 'get' lowered to const-0 placeholder
  (silent-null risk, Task #145)`.

This is not the older `n_modules=0` failure: this run retained the complete
module set through HIR and entered real MIR function lowering.

## Focused reproduction and root cause

Two ignored, lane-local fixtures reduced the failure below `values_equal`:
an enum-only match and a single explicit enum match both reach MIR statement 0
and terminate, while an adjacent `if` lowers. The common path copied
`HirMatchArm` composites into a fresh `norm_arms` array and then read
`norm_arms[i].pattern.kind`. The admitted Stage-2 engine erases the pushed
composite element shape at that boundary.

`lower_match_case` now detects explicit enum/wildcard-only arms on the original
carrier and calls `lower_enum_match` before constructing `norm_arms`. Binding
and mixed-pattern cases retain the normalization path. The source contract is
pinned in `bootstrap_binary_lowering_source_spec.spl`; execution evidence still
requires rebuilding the affected compiler provider.

The repository's mandatory three-cycle bootstrap cap was reached in the GPU
dynamic-loading lane. Do not retry this full bootstrap in the same session.

## Vulkan Engine2D verification consequence

The canonical readback wrapper cannot use Stage 2 directly because that
bootstrap CLI deliberately has no `run` command. A direct Stage-2
`native-build` of the wrapper-generated evidence program was attempted once.
It discovered and parsed all **189/189** modules, including
`backend_vulkan.spl`, `backend_vulkan_spirv_raster_blobs.spl`,
`sffi_vulkan.spl`, and `sffi.dynamic.spl`, then failed while storing the first
lowered HIR module:

```text
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
error: hir codec: no `HirTypeKind` arm for tag -1;
       regenerate src/compiler/20.hir/generated/hir_codec.spl
```

No evidence executable was produced, so Vulkan availability, device identity,
present, readback, and pixel parity remain **not executed**, not failed. The
generated source and raw wrapper evidence are under
`build/vulkan-engine2d-readback-gpu-r3/` (ignored build artifacts).

## Current-head follow-up: `eval_gt` (2026-08-24 UTC)

Fresh source `227049b0c4518e2173851692562eaf5e03a89a75` produced and admitted
Stage 2, then resumed Stage 3 from a planner-admission-v2 receipt. The compiler
crossed HIR 695/695, HIR finalization 950/950, post-HIR validation 695/695,
HIR reclamation, monomorphization, and post-monomorphization verification.
It entered MIR lowering and exited 139 at statement 0 of `eval_gt` in
`src/compiler/70.backend/backend/interpreter.spl`. The prior `values_equal`
frontier was therefore cleared, but the general carrier bug was not.

Retained evidence:

- `build/bootstrap/mustcheck-stage3-current/bootstrap-build-progress.events`
- `build/bootstrap/mustcheck-stage3-current/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- `build/bootstrap/mustcheck-stage3-current/stage3/x86_64-unknown-linux-gnu/memory-snapshot-v1.4004404.events`

The final retained snapshot reports 1,117,411,788 bytes peak tracked heap,
2,722,956 KiB RSS, and 2,742,140 KiB HWM. This is a MIR-lowering SIGSEGV, not
the older HIR memory termination.

The earlier direct-enum route still extracted elements of `[HirMatchArm]` into
untyped locals before accessing composite fields. Stage 2 stores such array
elements through ANY; the interpreter owner already documents the necessary
typed-local rebound for `[HirStmt]`. The owner fix now explicitly rebinds every
arm extraction on the direct, normalization, enum, and deep-enum routes as
`HirMatchArm`. This preserves the algorithm and removes no behavior or API.

The installed repository executable identified itself as a Rust bootstrap seed
when asked to run the focused source spec and lint, so those invocations are
rejected as acceptance evidence. Rebuilt Stage 2/3 evidence is required; the
same failed Stage 3 command must not be rerun against unchanged source.

### Cycle 2 result and final allowed fix cycle

The rebuilt compiler at `a02d01a1d9` passed the old `eval_gt` frontier and
continued through later functions, proving that typed arm rebinding corrected
one real carrier failure. It then exited 139 at statement 0 of the adjacent
`eval_gteq` nested enum match. HIR peak evidence improved slightly versus the
control: tracked heap 1,111,057,002 versus 1,117,411,788 bytes; RSS 2,715,972
versus 2,722,956 KiB; HWM 2,734,700 versus 2,742,140 KiB.

The remaining enum path copied every `HirBlock` body into
`enum_bodies: [HirBlock]`, then reread it after the same ANY-backed pushed-array
boundary. The final allowed fix cycle removes that redundant composite array
and obtains each body from the explicitly typed original `HirMatchArm` via the
already retained primitive source index. This changes O(number-of-arms)
composite copies to zero while preserving dispatch order and semantics.
