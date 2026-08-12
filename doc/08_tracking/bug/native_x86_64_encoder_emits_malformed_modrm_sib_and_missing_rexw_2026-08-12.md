# Pure-Simple x86_64 encoder emits malformed ModRM/SIB and drops REX.W (2026-08-12)

## Status: OPEN

## Summary

The pure-Simple native x86_64 encoder
(`src/compiler/70.backend/backend/native/encode_x86_64.spl`, reached via
`compile_native_x86_64` in `backend/native/mod.spl`) produces machine code that
segfaults for even the most trivial program. This was invisible until
2026-08-12 because `CodegenTarget.Host` fell through `compile_native`'s match to
`compile_native_stub`, so the encoder had **never actually run** on a
native-build. See
`doc/08_tracking/bug/stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11.md`
for that history and for the harness used to reach this lane.

## Repro

Fixture `p.spl`:

```
fn main() -> i64:
    0
```

Built through the pure-Simple lane with `--backend native` (see the companion
bug doc for the exact driver-script method). The build now succeeds and links,
producing a 20752-byte binary that segfaults with SIGSEGV (exit 139).

## Evidence — disassembly of the generated `main`

```
0000000000001ed0 <main>:
  1ed0: 55                push   %rbp
  1ed1: 48 89 e5          mov    %rsp,%rbp
  1ed4: 48 81 ec 20 00 00 00  sub $0x20,%rsp
  1edb: 48 89 4c 89 48    mov    %rcx,0x48(%rcx,%rcx,4)   <-- WRONG
  1ee0: bb 00 00 00 00    mov    $0x0,%ebx
  1ee5: 00 00             add    %al,(%rax)               <-- stray
  1ee7: 00 00             add    %al,(%rax)               <-- stray
  1ee9: 49 89 dc          mov    %rbx,%r12
  1eec: 4c 89 e0          mov    %r12,%rax
  1eef: 48 8b 4c 8b 48    mov    0x48(%rbx,%rcx,4),%rcx   <-- WRONG
  1ef4: 89 ec             mov    %ebp,%esp                <-- WRONG (no REX.W)
  1ef6: 5d                pop    %rbp
  1ef7: c3                ret
```

Three distinct defects:

1. **Frame-slot store `48 89 4c 89 48`** decodes as
   `mov %rcx,0x48(%rcx,%rcx,4)`. A store of `%rcx` to a `%rbp`-relative frame
   slot should be `48 89 4d f8` (`mov %rcx,-0x8(%rbp)`). The encoder emitted a
   ModRM byte selecting a SIB form and then a wrong SIB/displacement, so the
   effective address is computed from `%rcx` scaled by 4 rather than from the
   frame pointer.
2. **Frame-slot load `48 8b 4c 8b 48`** is the identical bug on the load side
   (`mov 0x48(%rbx,%rcx,4),%rcx`).
3. **Epilogue `89 ec` (`mov %ebp,%esp`) is missing REX.W** — the 64-bit form is
   `48 89 ec`. Writing the 32-bit form zero-extends and destroys the upper 32
   bits of `%rsp`, which alone is fatal.

The prologue (`push %rbp` / `mov %rsp,%rbp` / `sub $0x20,%rsp`) and the
register-to-register moves (`49 89 dc`, `4c 89 e0`) are encoded correctly, so
the fault is specific to (a) `%rbp`-relative memory operand encoding and (b)
REX.W emission on the epilogue stack restore.

## Impact

The pure-Simple native backend (`--backend native`) cannot produce a working
executable for any program. The default `llvm` backend is unaffected — it never
calls `compile_native`. This does not block the default build lane, but it means
the self-contained "no external toolchain" native path advertised in
`backend/native/mod.spl`'s header comment is non-functional.

## Next step

Audit ModRM/SIB construction for base-`%rbp` displacement operands and the REX.W
predicate in `encode_x86_64.spl`. Note that `%rbp` as a ModRM base requires
mod!=00 (a displacement is mandatory), and `%rsp`/`r12` as a base requires a SIB
byte — mishandling of exactly those two special cases matches the observed
output. A byte-level encoder unit spec over a handful of known-good instruction
encodings would catch all three defects immediately and does not exist today.
