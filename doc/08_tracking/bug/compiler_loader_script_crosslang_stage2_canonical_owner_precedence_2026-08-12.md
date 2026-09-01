# Stage2 canonical-owner precedence failures remain after cd0277

## Status

Open; active blocker for `compiler_loader_script_crosslang_perf`. The feature is
not dev-done and Stage2 admission was not granted.

## Reproduction

The isolated Stage2 command was run from source head
`cd0277de18e722bab990cefdf12da63c07e41999`. It exited `2` without emitting an
admissible Stage2 executable. The retained diagnostic log is:

`/mnt/data/bs2/perf-integrated-cd027/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`

Log SHA-256:

`c9c10ba878b0f2154efcddf25fc1bb91949e79790141fc402a3b81598039d07d`

## Evidence

The native-build summary reports **46 failed files**, improved from **65** in
the prior `eda2d6ce920` attempt. The dominant family is **29 `ANY`**
canonical-owner/type-precedence failures; the remaining 17 failures are
non-`ANY` receiver/field-owner diagnostics. The failure shape remains a
per-file HIR lowering inability to establish the canonical struct owner/type;
the reduction is diagnostic progress, not an admitted compiler result.

## Unblock condition

Propagate an explicit canonical field-layout owner/proof (or stable owner ID)
from declaration/import/call-return construction through HIR to MIR, preserving
fail-closed behavior for unknown and non-struct carriers. Then run one fresh
bounded Stage2 admission attempt and retain its exact exit, output absence or
hash, and failure census. Do not claim performance or Stage4 evidence until
Stage2 is emitted and admitted.
