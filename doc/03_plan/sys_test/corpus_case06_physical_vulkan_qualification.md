# Corpus case 06 physical Vulkan qualification

REQ-2D-006 and NFR-2D-002 require the real Web source path to reach both
renderers on a physical Linux Vulkan device. Case `06-rectangular-clip` is the
second bounded corpus scene. The pinned source HTML SHA-256 is
`2c4677447453c4576f559a380d6585c3ddd1e14abbef7c77ac40a33dc1732000`;
the independent reference HTML SHA-256 is
`ce0a659f466f71494f6672b44ecf4ad7f239652837ac33da78d8d2bb84a558c2`.

At 640 × 480 and DPR 1, the authored parent spans x40..199 and y40..139.
Its child spans x80..299 and y65..234, so the effective cyan `#00aaff`
pixels are x80..199 and y65..139. All other pixels are opaque white. The
independent 1,228,800-byte RGBA oracle has SHA-256
`0372ef52c5e58dfa59d71239609526592e022a00419f25e3eebc902d083debb1`.

## Admission and execution

The Web producer must render the pinned HTML and retain its original DrawIR
digest and source-command indexes. Case 06 admission must inspect every
emitted command, reject unsupported paint/style/effects, and carry the actual
parent overflow clip to the child GPU rectangle. It must not replace the Web
producer with the reference rectangle. The full-target `#scene` clip may be
ignored only after admission proves it covers the complete target.

Both isolated workers consume the same admitted GPU DrawIR and produce
completed readbacks. The Engine2D and Skia owner adapters bind the case 06
fixture and source/reference pins, scene scope, completion, and device
identity. The candidate verifier checks both 640 × 480 captures against the
independent oracle, compares every pixel and device/driver UUID, and retains
source and GPU DrawIR digests plus command mapping. Offline receipts remain
candidates and cannot prove fresh physical execution.

On a qualified Linux GPU host, use a compiled worker and authenticated pinned
Skia provider:

```text
sh scripts/check/check-vulkan-2d-qualification.shs <absolute-qualified-executable> <absolute-skia-provider> build/test-artifacts/vulkan_2d/<fresh-id> corpus-case06
```

## Evidence and open gate

The oracle, source admission, owner adapters, worker entrypoints, and focused
specs exist. Static source/reference/pixel hash checks and scoped whitespace
checks are the current evidence. The actual Web producer command inventory,
Simple specs, pinned Skia native build, and dual physical GPU captures have
not passed in this workspace. Case 06 cannot be promoted until those gates
pass; the remaining corpus cases require their own source and rendering
qualification.
