# Stage2 NVFS close reaches a named collection-remove runtime trap

Status: ABI-matched Stage2 runtime and focused owned-device behavior pass;
pure-Simple shadow gate remains pending. The full compiler matrix failed later
at the full CLI link boundary for separate optional-runtime symbols.

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
entrypoint. C syntax checking passed. The fresh Stage2 admission published an
immutable runtime capsule whose SHA-256 is
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
The capsule verifier passed. Against that capsule, the no-stub native probe
compiled 49 files with zero failures, linked a 211 KB executable, and exited
zero with create/close and owner-count output `true`, `true`, `0`, `0`.
Evidence is retained in
`build/mini_builds/target56_stage2_owner_probe/build_owned_device_current.log`
and `probe_owned_device_current`. This is focused behavioral proof, not a
pure-Simple runtime shadow or full matrix PASS.

## Next proof

Run the pure-Simple runtime representation probe and dual-run shadow gate.
Repair the separate full CLI link failure and require the Stage2 matrix's five
mandatory PASS rows before Stage3/4. The old capsule's named trap is not a
verdict on this updated implementation.
