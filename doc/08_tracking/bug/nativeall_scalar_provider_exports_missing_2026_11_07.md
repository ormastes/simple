# Native-all raw scalar provider exports

Source candidate on `work/nativeall-scalars-d88f`, based on
`7cec6a54ea8a2e0f1be4bbc215685fb688f802d2`. Root owns the canonical bug claim
`01a1afac/nativeall-scalars` and eventual publication. This document does not
close the claim or qualify a compiler phase.

The retained Windows native-all link is missing `__simple_pow`, `rt_time_ms`,
and `rt_host_commit_headroom_bytes_v1`. All three contracts pass raw i64 values.
The change selects a one-symbol native-all power provider over the exact shared
integer algorithm, adds the Rust wall-clock millisecond export over its actual
C Unix-microsecond owner, and moves the exact typed commit query into the
existing narrow memory-headroom provider. C core clocks remain unchanged.

## Composition and cache ownership

| Composition | Selected provider |
|---|---|
| Rust runtime/native-all | memory-headroom C TU; native-all alone adds power TU; Rust time export |
| Simple core and compatibility runtime lists | existing memory-headroom TU; existing core intrinsic owner |
| Rust native-project core supplemental archive | existing memory-headroom TU; existing intrinsic owner |
| Core bootstrap capsule | existing memory-headroom TU |
| Manual P3 frozen list | existing memory-headroom TU and intrinsic owner |
| SimpleOS x86_64 and aarch64 sysroot loops | add memory-headroom TU beside runtime_native |
| Standalone aarch64 and riscv64 sysroot loops | add memory-headroom TU beside runtime_native |

On baremetal both headroom functions return zero. Their only public definitions
are in the selected memory-headroom TU. The four loop additions preserve the
previous commit-headroom fallback without adding OS dependencies. Existing
freestanding flags remain intact.

Cargo watches the runtime tree and explicitly names the new power C/H inputs.
The Rust core archive input list now names the new helper header. Simple POSIX
object keys hash all runtime C/H contents; Windows keys hash preprocessed TUs.
The manual P3 shadow copies the complete runtime directory and recompiles it.

## Evidence and limits

Diagnostic artifacts are retained under
`C:/dev/simple/.git/worktrees/nativeall-scalars-d88f/evidence/`.
See the companion SDN receipt for statuses and attempts.

Actual native-all and core power providers executed defined-domain assertions
under signed-integer-overflow UBSan. This does not define signed overflow for
unrepresentable powers. The actual Rust time module executed five tests linked
to real clock/timestamp C owners. The Windows SDK smoke queried the live OS.
The actual headroom TU cross-compiled with repository libc headers for all
three baremetal architectures; symbol inventories contained exactly its two
public headroom exports. These results do not qualify a baremetal image.

Historical pointer mapping returned FAIL: ten Windows backslash paths mismatch
the identical ten slash-normalized baseline rows. The checker correction landed
separately in PR #7336; this receipt does not claim a corrected rerun.
Unsafe-backlog returned FAIL with INCOMPLETE_INPUT_INVENTORY: sparse checkout
omitted 26,229 tracked test Simple files. Its source-only inventory reported
migration 3698/3546, but cannot establish the full-tree result. No modified file
in this repair is a Simple inventory input. Neither baseline is changed here.
The host map and targeted C contract checks passed. The full native-all link,
P2/SSpec, global compiler/lib/MCP checks, and bootstrap admission remain UNRUN.
