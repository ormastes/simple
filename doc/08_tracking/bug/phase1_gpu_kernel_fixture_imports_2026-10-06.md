# GPU kernel fixture imports prevent discovery

The kernel-table bucket fixture used bare `common.gpu.engine2d` imports although its owners are in `std.common.gpu.engine2d`. The diagnostic Phase 1 sweep retained an unresolved-import failure with zero examples at ordinal 07312. Both imports now resolve through the existing standard library owners; production code and original assertions are unchanged.

An isolated Phase 1 verification executed 20 assertions: 20 passed, zero failed. Producer SHA-256: `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`; frozen owner source: `e59027c353e9ed6ea8ddf572424da70e188fe511`, plus the two-import fixture patch. Receipt: complete, exit zero, quiescent tree, peak RSS 271,780 KiB under the 1,048,576 KiB cap. Evidence remains in `/tmp/simple-phase1-kernel-import-repair/evidence/`.

This is bootstrap Phase 1 diagnostic evidence, not self-hosted or whole-suite qualification. A generated scenario directory encountered a filename-length warning; actual named assertion results were retained.
