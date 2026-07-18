# rv64 freestanding C runtime silently lacks core_string.spl runtime fns

- **Date:** 2026-06-15
- **Severity:** P2 (link-time, caught by from-source link; was masked by `--allow-prebuilt-artifact`)
- **Area:** compiler / baremetal runtime closure (riscv64-unknown-none)

## Symptom

Linking the rv64 SimpleOS web-server closure from source (no
`--allow-prebuilt-artifact`) fails with undefined symbols `rt_string_to_int`
and `rt_contains`. Codegen emits bare runtime calls to these (int-parse / `in`
operator lowering), but the rv64 freestanding closure links the hand-written C
runtime `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`, NOT the
pure-Simple `src/runtime/simple_core/core_string.spl` (which DOES define both as
`pub fn`).

The C runtime defines most string rt_* siblings (rt_string_find, rt_string_trim,
rt_string_new, rt_native_eq, ...) but had drifted out of sync — it was missing
these two. Because the canonical archive `build/simple-core/libsimple_runtime.a`
DOES define them (each in its own section), prior prebuilt-artifact link paths
never exercised this gap.

## Root cause (the real gap)

There are two parallel runtime implementations of the same rt_* ABI:
1. `src/runtime/simple_core/core_string.spl` (pure-Simple, canonical)
2. `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (hand-written C, used
   by the baremetal/freestanding link closure)

They can silently diverge: a function added to (1) is not reflected in (2), and
nothing fails until a from-source freestanding link references it.

## Workaround applied (this change)

Added correct C implementations of `rt_string_to_int` (inline base-10 parse;
freestanding has no libc strtoll) and `rt_contains` (substring via
rt_string_find, array membership via rt_native_eq) to the C runtime, mirroring
the core_string.spl semantics. Raw-int return convention matches sibling C rt_*.

## Suggested real fix (follow-up)

- Generate the freestanding C runtime symbol surface from the same source of
  truth as core_string.spl, OR
- Add a build-time parity check that diffs the `pub fn rt_*` set in
  core_string.spl against the defined symbols in freestanding_runtime.c and
  fails the baremetal build on drift, OR
- Make the rv64 freestanding closure compile core_string.spl directly so there
  is one implementation.

## Triage note (2026-07-17)

Likely fixed by commit `7c30ce49d04f` which adds the missing `rt_string_to_int` and `rt_contains` implementations to the freestanding C runtime, resolving the link-time undefined-symbol gap. Pending runtime verification: link and run the rv64 SimpleOS web-server closure from source with zero undefined symbol errors.
