# arm64 kernel unwrap_or/unwrap ignore Result ordinal Ok=0/Err=1 (hosted parity gap)

- **Status:** open
- **Found:** 2026-11-23, Opus review of the arm64 `rt_unwrap_or_value` shim (PR for `work/a64-unwrap-or-20261123`)
- **Scope:** SimpleOS freestanding runtimes; arm64 confirmed, other arches share `rv_unwrap_or_pick`

## Symptom
The hosted `rt_unwrap_or_value` (`src/runtime/runtime_native.c:6881`) treats only
Result enum ids (via `rt_is_result_enum_id`) as Result and accepts both the hashed
Ok/Err discriminants and the ordinals Ok=0 / Err=1.

The freestanding path does something different. `rt_unwrap_or_trap` in
`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c` (~6773) and the
shared `rv_unwrap_or_pick` (`src/os/kernel/arch/common/rt_value.spl`) match only
the hashed Ok/Err discriminants, on any enum id.

## Impact
On the kernel, an ordinal-encoded `Err(e).unwrap_or(d)` returns the Result wrapper
instead of `d`, and `Err(e).unwrap()` does not trap. A user enum whose
discriminant equals the Ok/Err hash would be unwrapped, where the hosted runtime
would not.

## Fix direction
Change `rv_unwrap_or_pick` and the arm64 C `rt_unwrap_or_trap` together to match
hosted: Result ids only, ordinal and hashed discriminants. Add an executable case
to `test/01_unit/os/multiarch/arch_common_rt_value_spec.spl`.
