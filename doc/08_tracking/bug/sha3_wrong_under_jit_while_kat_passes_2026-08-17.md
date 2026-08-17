# SHA3 returns wrong digests under the JIT while its KAT passes 7/7

- **Filed:** 2026-08-17
- **Severity:** P1 — a cryptographic hash silently returns wrong values on the
  engine that ordinary programs run on, and the test that exists to catch this
  cannot reach that engine
- **Status:** OPEN, independently CONFIRMED by measurement

## Summary

`SHA3-256` under the **Cranelift JIT** returns digests that do not match the NIST
vectors. The **interpreter is correct**. `sha3_kat_spec.spl` measures
`Results: 7 total, 7 passed, 0 failed` and is **structurally incapable** of
detecting this, because `bin/simple test` runs the tree-walk interpreter while
`bin/simple run` uses the JIT.

A passing crypto KAT is therefore actively misleading here: it certifies the one
engine that was never in doubt.

## Measured evidence

Binary for every number below: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
the Rust seed, 59,536,728 bytes, mtime 2026-08-16 22:59. Probe kept in its own
minimal file (one unsupported operation silently demotes a whole program to the
interpreter, which would hide the defect). `rc` read on the line AFTER the
command, never through a pipe. Both arms `rc=0`.

| value | `SIMPLE_EXECUTION_MODE=interpreter` | `=jit` |
|---|---|---|
| control `2^60` | `1152921504606846976` | `-1152921504606846976` |
| SHA3-256("") | `a7ffc6f8bf1ed766…` (NIST) | `c0e8cca89df588f3…` |
| SHA3-256("abc") | `3a985da74fe225b2…` (NIST) | wrong |
| SHA3-512("abc") | correct 64 bytes | **first 32 bytes byte-identical to its own wrong SHA3-256("abc")** |

The `2^60` control is load-bearing: it diverges, which proves the JIT arm
actually ran rather than being silently demoted to the interpreter.

The SHA3-512/SHA3-256 prefix identity is the strongest single clue — a numeric
slip does not make one function's output a prefix of another's. It points at a
shared corrupted buffer or a mis-sized read, not at the sponge arithmetic.

## Probable family, not a `sha3.spl` defect

The `2^60` control diverging in the same run puts this with the **61-bit
boxed-int truncation** family: the inline form is `v<<3` plus a 3-bit tag, so any
`|v| >= 2^60` loses its top bits. That family already spans roughly ten filed
docs. Do NOT patch `sha3.spl` before testing the family hypothesis — a local fix
there would mask the shared cause and leave every other consumer wrong.

## Related new finding, same session

**`text.substring` is also corrupt under the JIT** — a hex renderer built on it
returned whole 8-character table chunks instead of per-byte slices. This is not
on the previously published list of divergent builtins and deserves its own row.

## Why the test suite cannot catch this class

`test` is the tree-walk interpreter; `run` is the Cranelift JIT. 711 of 23,958
spec files call at least one method that is known to diverge between the two, and
they would all stay green through any JIT regression. See
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.

For anything cryptographic this is not a theoretical gap: the KAT is the control,
and the control is blind on the engine that matters.

## Reproduce

Write a minimal `.spl` printing the digest bytes, then run it twice and diff:

```sh
SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl > a.out
rc=$?
SIMPLE_EXECUTION_MODE=jit bin/simple run probe.spl > b.out
rc=$?
diff a.out b.out
```

Keep the probe minimal and in its own file. Include a `2^60` value as a control so
a silent demotion to the interpreter cannot read as "no bug".

## Required fix shape

1. Establish whether the 61-bit truncation family explains it. If so, fix the
   family, not `sha3.spl`.
2. Ship a **subprocess cross-engine** spec — a spec body alone runs interpreted
   and can never go red on this. Copy the pattern in
   `test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl`.
3. Prove causation by ablation: apply, verify, then REMOVE the fix and confirm
   the wrong digests return.
