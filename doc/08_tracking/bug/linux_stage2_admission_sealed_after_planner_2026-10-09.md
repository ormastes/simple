# Stage 2 admission remained mutable after planner failure

Linux aarch64 bootstrap at `3d7141f912c` built Stage 2 and passed its sanity and
receiver probes, then planner construction failed. The next attempt at
`6f7bb4380ba2` stopped before compilation with
`bootstrap-cache-error: prior directory is not sealed nonsymlink evidence`.
The retained `stage2-admitted` directory was mode 0700, although its compiler
and admission receipt were already read-only.

Runtime binding and `chmod 500` occurred after fallible parent/planner receipt
publication. Move the completed Stage 2 runtime-binding/snapshot/sealing block
before those dependent publishers. A later planner failure then retains sealed
Stage 2 evidence that the existing archiver can preserve unchanged. The archive
validator remains strict; no mutable old directory is silently treated as sealed.

The archive regression test asserts the publication ordering, executes the
production finalization block with a runtime-binding fixture, simulates a
downstream failure, then uses the real sealed-tree validator, archive helper,
and manifest verifier on the resulting admission. Existing malformed, mutable,
symlink, collision, and tamper refusals remain covered.

Validation passed: the archive regression, runtime-capsule contract (POSIX,
Windows, macOS and diagnostic Cocoa cases), and all three parent-receipt
candidate-binding checks. The capsule fixture was updated to include the four
script/test roots now required by canonical source snapshots; its previous
failure was missing fixture roots, not a runtime-capsule policy failure.

Original evidence: `/home/yoon/dev/simple-release-1.0-codex/build/native_probe/linux-arm-phase3-20261009/bootstrap-attempt2.log`
and `bootstrap-attempt3.log`. No additional full bootstrap has been run: the
thread reached its three-cycle limit. Existing failed-run evidence and compiler
caches remain preserved; recovery of that prior unsealed directory is separate
from preventing new unsealed publications.
