<!-- codex-research -->
# Pure Simple Profile-Guided Executable Optimization Feature Options

Date: 2026-06-01

## Option A: Loader-First `.sprof` Profile Consumption

Description: implement `.sprof` validation, merge, and opt-in load for the
optimize app and startup loader. Native/bare-metal counters remain planned.

Pros:
- Lowest risk first implementation.
- Gives every later optimizer a common profile source.
- Aligns with existing schema-first work.

Cons:
- Does not by itself improve native executable layout.
- No bare-metal counter implementation yet.

Effort: Medium, 6-10 files.

## Option B: Native Counter + Pure-Simple Layout Optimizer

Description: add native function/block/edge counters and a pure-Simple
BOLT-like layout pass that reorders Simple executable metadata from `.sprof`.

Pros:
- Directly targets native executable speed.
- Avoids external BOLT dependency.
- Creates measurable before/after executable evidence.

Cons:
- Requires stable symbol/relocation/layout metadata.
- More risk to executable startup and native build flows.

Effort: Large, 12-18 files.

## Option C: Full MDSOC+ Profile Optimization Capsule

Description: implement the full architecture as phased capsules: `.sprof`
loader, native counters, pure-Simple executable layout optimizer, and
bare-metal software-breakpoint counter capsule with auto-disarm.

Pros:
- Matches the full user request.
- Gives interpreter, loader, native executable, and bare-metal one coherent
  profile-guided optimization story.
- Prevents one-off counters from bypassing safety policy.

Cons:
- Largest design and verification matrix.
- Requires careful staging to avoid destabilizing native and bare-metal paths.
- Needs hardware/QEMU evidence before claiming bare-metal wins.

Effort: XL, 20-35 files over multiple slices.

## Recommended Selection

Choose Option C for the architecture/plan, but implement in release-sized
slices: A first, then B, then the bare-metal subset of C.
