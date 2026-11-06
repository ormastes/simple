# Seed JIT: `text.from_bytes(b)` repro overflows the stack in the debug build

- **Status:** FIXED (already, by `bfe4c8cb879`, PR #7213) — verified 2026-11-06
  on branch `work/seed-jit-batch3-20261106`; regression test added.
- **Found:** 2026-11-06 by the seed interpreter lane (PR #7240,
  `seed_interp_text_from_bytes_static_2026-11-06.md`: "the debug-build seed
  JIT overflowed its stack on this file on this host; not investigated").
- **Engine:** Rust seed Cranelift JIT.

## Symptom

`test/fixtures/seed_interp/text_from_bytes_static_repro.spl`
(`val b: [u8] = [97u8, 98u8, 99u8]` / `print("text_from_bytes " + text.from_bytes(b))`),
`SIMPLE_EXECUTION_MODE=jit`, debug seed:

```
thread 'simple-main' (18760) has overflowed its stack
```

exit 139.

## Root cause

Not a recursion in the compiler. Cranelift had no lowering arm for the builtin
text statics, so `text.from_bytes(b)` was emitted as a call to the sanitized
dotted name `text_dot_from_bytes`, which is deliberately absent from the
static provider manifest. The JIT jumped through that unusable import; on this
Windows host the resulting wild call surfaces as a stack overflow of the
`simple-main` thread (elsewhere as SIGSEGV / access violation). Same defect as
`seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`, fixed by
`bfe4c8cb879` ("fix(seed-jit): route text.from_char_code/from_bytes to the
runtime ABI", `src/compiler_rust/compiler/src/codegen/instr/calls.rs`, routing
to `rt_bytes_to_text`). PR #7240 measured against a seed built from
`ecb705896a4`, which predates that commit.

## Evidence (debug seeds unless noted, same host, same repro file)

| seed source | `SIMPLE_EXECUTION_MODE=jit` |
|---|---|
| `ecb705896a4` (PR #7240's measurement base) | `thread 'simple-main' has overflowed its stack`, rc 139 |
| `ecb705896a4` + only `bfe4c8cb879` cherry-picked | `text_from_bytes abc`, rc 0 |
| `release/1.0.0` @ `a58d06d80d3` | `text_from_bytes abc`, rc 0 (5/5 runs) |
| PR #7240 head `bc12cc120b7` | `text_from_bytes abc` (jit, interpret, default `run`) |
| this branch (`release/1.0.0` + batch-3 fixes), **release** profile | `text_from_bytes abc`, rc 0 (interpret: "variable text not found" until PR #7240 lands) |

Also checked on `a58d06d80d3`, no overflow: untyped `[u8]` local, inline
literal argument, `simple <file>` without `run`, run from the repo root.

## Resolution

No code change needed on `release/1.0.0`. Added
`compiler/tests/text_static_builtins_jit.rs::text_from_bytes_of_typed_u8_local_concatenates`
pinning the exact repro shape (typed `[u8]` local + concatenation); it passes
on `a58d06d80d3` (the fix is already present) — the "before" evidence is the
`ecb705896a4` seed run above.
