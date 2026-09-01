# Stage-2.5 misbinds streaming surface Option unwrap to Poll

Status: source fixed; bridge rebuild is blocked by a producer-specific
frontend-core aggregation timeout.

The source-corrected Stage-2.5 intermediary SHA-256
`37a15c5d0fe0c4b0b4cfb70509ad4bce148a200d48e9e95aaa00636e275f221d`
completed all 687 canonical surface files, then crashed between parse and HIR.
Kernel PC `0xdc32ea` maps to `hir_cache_closure_digest`, at its first field
load from a null `ModuleSurfacesByName` argument.

The caller in `driver_hir_pipeline_lowering.spl` extracted
`streaming_module_surfaces_owner.unwrap()`. Stage-2.5 disassembly at
`0xdc6c77` shows that call resolving to `Poll.unwrap`, the same self-host
method-collision class as the earlier bootstrap-entry failure. Source now uses
an explicit `Some(surfaces)` helper and fails closed on an absent/empty owner.

Resume with a hash-recorded diagnostic copy of Stage-2.5 whose one proven bad
call target is redirected to `rt_enum_payload`; use it only to emit the
source-corrected next intermediary. Then run the exact canonical Stage-3
contract without binary patching. Preserve the cache and three-cycle cap.

## Bridge rebuild result

The diagnostic Stage-2.5 copy SHA-256
`3bd5a3a5a00663e20c5c83ac331634dd5f453a3152909005fecd30c075d04845`
retargeted only the proven streaming-owner call at `0xdc6c77` to
`rt_enum_payload`; disassembly verified the target. Its full source-corrected
bridge rebuild used a fresh producer-scoped cache, strict no-stub mode, a
600-second per-file limit, and an 1,800-second outer bound. It failed with
exactly one file:
`src/compiler/10.frontend/core/__init__.spl: timeout (600s)`.

The older patched Stage-2 producer compiled this deduplicated file and emitted
Stage-2.5 successfully, while Stage-2.5 times it out. This is a
producer-specific compile-performance regression, not evidence that the 203
duplicate exports returned. Retained cache:
`build/bootstrap/abnormality-source-stage26/native-cache`; final log:
`build/native_probe/abnormality-source-stage26-streaming-fix.log`.

Next owner action is to profile the Stage-2.5 compilation of this one facade
against the successful older-producer receipt and identify the regressed phase
or algorithm. Do not raise the timeout or repeat the unchanged build.

## Canonical direct-bridge evidence

Avoiding the noncanonical full facade, the one-call Stage-2.5 diagnostic copy
ran the canonical 687-file Stage-3 closure directly. It passed the repaired
streaming-owner boundary and began HIR lowering. The first cache store failed
closed in `hc_enc_visibility`. A bounded GDB replay proved the exact value and
stack: raw visibility `0`, `rt_enum_discriminant=-1`,
`HirModule -> SymbolTable -> HirSymbol -> visibility`. This is a genuinely
invalid non-optional field, not a missing codec variant.

`HirSymbolTable.define` now normalizes only invalid visibility payloads to
`Visibility.Private`, preserving all six valid scoped variants and preventing
any accidental access widening. The final diagnostic bridge may encode the
same invalid legacy payload as Private solely to emit this source correction;
the unpatched next-stage candidate must then pass the canonical codec path.

## Final bounded cycle result

The final cycle used diagnostic bridge SHA-256
`0b1f731519e7da51fba30e1adcb8d0d91c230e37a46cc507e9154036bdc487aa`,
whose only additional diagnostic behavior maps the already-proven invalid
legacy visibility payload to the existing Private encoding arm. It completed
all 687 canonical surface files and entered HIR after 958,645 ms, proving the
visibility correction advanced the build. The next cache store then failed
closed with `hir codec: no ScopeKind arm for tag -1`.

This is a second invalid raw enum payload in the same serialized HIR object
graph. No output executable was admitted, and the diagnostic bridge is not an
admitted compiler. Retained log:
`build/native_probe/abnormality-source-stage3-visibility-bridge.log`; retained
cache:
`build/bootstrap/abnormality-source-stage3-candidate/native-cache-visibility-bridge`.
The three-cycle guard is exhausted. Resume in a fresh scoped session by
proving the construction site and intended fail-closed fallback for
`ScopeKind`; do not add a codec-wide wildcard or repeat this command unchanged.
