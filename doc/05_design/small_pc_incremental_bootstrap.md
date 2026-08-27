# Small-PC incremental bootstrap detail design

## Worker propagation

Add `CARGO_BUILD_JOBS="${jobs}"` to all four `env -i` branches in `run_rust_authority_cargo`. A source-contract test requires exactly four exports, preventing an LLVM/non-LLVM or LTO branch from escaping the cap.

## Aggregate-copy safety

In LLVM, derive `tag_mask=7` and `untag_mask=!7`; require `tag==TAG_HEAP` and nonzero payload. Select the fresh zero-filled destination for invalid sources and explicitly select zero for copied words. Deep fields use the full tag mask. This mirrors the existing Cranelift implementation.

## Verification and rollback

Run the focused authority contract and LLVM Cargo check, then one cache-preserving full bootstrap with `--jobs=min`. Require Stage 4 essential-tool markers and deployed-binary hash/provenance. Roll back by redeploying retained `bin/release/x86_64-unknown-linux-gnu/simple.pre_deploy` and rerunning `-c 'print(1+1)'`.

## Stage3 ownership

Stage3 streaming surfaces require `SIMPLE_STAGE3_STREAMING_SURFACES=1` together
with bootstrap, AOT, resolved entry-closure, and non-VHDL gates. The producer
records the opt-in in both its transcript and cache fingerprint. Ordinary AOT
and Stage4 retain their independent admissions. A non-streaming control was
OOM-killed; the streaming run must prove parity through Stage4 before release.

Closure discovery is also inside the Stage3 streaming boundary. Each source's
text import scan runs in a transient scope, promotes only its compact import
path result, and ends before resolver/source/set/queue mutations begin. This
keeps persistent mutations outside transient ownership and avoids retaining the
broad scanner graph that left a 2.24 GiB base in the first implementation.

Stage3 keeps declaration arenas enabled from the first surface parse, avoiding
the legacy environment mirror's per-field `setenv` allocation leak. Compact
surface construction remains transient; the finished surface alone is promoted,
the scope is reclaimed, and only then is persistent builder state mutated. The
core-C transient raw-allocation side table is also released after a large scope
instead of pinning its geometric peak capacity; glibc builds trim the released
pages so the parser high-water mark does not remain resident. Non-entry modules then promote
only the reduced flat-MIR registry; their full HirModule graphs are reclaimed.
Stage4 remains unchanged.

At the paused ownership boundary, parser reset releases the backing storage of
persistent global arena arrays while keeping the array owners alive. Reset-time
replacement storage is persistent because paused scopes assign scope id zero;
scope end then reclaims only transient parser children. A per-scope release bit
defers glibc trimming until after both arena backing storage and transient raw
objects have been freed, so trimming cannot run too early to return those pages.
