# Stage2 NVFS close reaches a named collection-remove runtime trap

Status: source repair added; ABI-matched runtime and behavioral verification pending.

## Reproduction

The isolated `build/mini_builds/target56_stage2_owner_probe/main.spl` calls
`NvfsPosixDriver.new_on_owned_device` with a memory block device, then closes
the driver. The historical admitted Stage2 binary with SHA-256
`5d71c26b371b83d0041e10b815dae153a38b9f7c61aa0931f3473aaee919e2f6`
compiled 49 reached files with `SIMPLE_NO_STUB_FALLBACK=1`, failed zero, and
linked a 211 KB probe. Its symbols include
`NvfsPosixDriver.new_on_owned_device`. Running the probe printed `true` for
device creation, then aborted with the named
`rt_collection_remove` trap (exit 134) during close. The retained evidence is
under `build/mini_builds/target56_stage2_owner_probe/`.

The capsule used by that probe predates the current branch's runtime source.
The branch also rebased over later `main` commits after the Stage2 candidate
was admitted, so this candidate cannot certify the present source revision.

## Source repair

`runtime_native.c` now dispatches collection removal to its existing
`rt_array_remove` for tagged array indices and to dictionary lookup/deletion
for dictionary keys, returning the removed element/value. The pure-Simple
`simple_core/core_array.spl` owner implements the same ABI for its ordinary
and byte-packed arrays and dictionaries. The existing representation probe
now asserts a second array removal and dictionary value/removal behavior.
The prior static test that demanded the named trap now demands the concrete
entrypoint. C syntax checking passed. No updated runtime capsule or native
behavioral PASS exists yet; an attempted `check` with the historical Stage2
CLI was unsupported, and the available repo `bin/release` binary identified
itself as a Rust bootstrap seed and failed in its own JIT before checking this
source.

## Next proof

Build a fresh ABI-matched current-source Stage2 runtime and compiler in the
isolated worktree, with the unchanged RSS cap and supported observer budget.
Run the owned-device probe against that immutable capsule and require create
and close to pass. Run the pure-Simple runtime representation probe and the
dual-run shadow gate. Then rerun the Stage2 compiler-test matrix and require
its five mandatory PASS rows before Stage3/4. Do not cite the old capsule's
named trap as a verdict on the updated implementation.
