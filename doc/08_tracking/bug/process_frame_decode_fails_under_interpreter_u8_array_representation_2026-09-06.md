# `decode_process_transfer_frame` rejects a byte-identical `[u8]` built with `as u8` — interpreter-only, breaks the whole piped parent-commit transport

- **Filed:** 2026-09-06
- **Area:** compiler / interpreter — `[u8]` element representation; structural transfer codec
- **Severity:** the entire `SPRF1` text-line process transport is dead on any run
  that falls back to the interpreter. Frames are transmitted and hex-decoded
  perfectly, then rejected as `invalid-envelope`.
- **Blocks:** `test/03_system/plan_acceptance/parent_authoritative_actor_process_spec.spl`,
  example "Obtain an admitted pure-Simple native verdict." (1 of its 3; the other
  two pass).

## Symptom as first seen

The acceptance example reports `accepted=0 receipt_ok=false
reason=empty-process-result-batch after_revision=1 summary=3 check(s) failed`.
The reader's poll shows `accepted=0 rejected=1` with an empty reason — the frame
reaches the parent and is refused at admission.

## What was ruled out (each by a probe under
`src/compiler_rust/target/debug/simple run`)

1. **Not the macOS `/proc` gap.** `process_spawn_piped` + `process_read_stdout` +
   `process_is_piped_alive` + `process_close_piped` all work here:
   `pid=50029 … chunk_len=11 alive=false … total=HELLO-PIPE … closed=true`.
2. **Not the pipe.** The 246-char `SPRF1 …` line arrives byte-identical
   (`sent_len=246 got_len=247` incl. `\n`, `equal=true`) and decodes with
   `decoded_ok=true`.
3. **Not line reassembly.** Rebuilding the line one character at a time —
   plain local var, and again as a class field with the same shape as
   `ParentCommitPipedResultReaderV1.pending` — yields `equal=true` and
   `decoded_ok=true`.
4. **Not the multi-line boolean** at
   `src/lib/nogc_async_mut/parent_commit_piped_process.spl:203-204`, nor the
   `var decoded_wire: [u8] = []` branch-assignment shape, nor
   `max_line_bytes` (8,388,726 — the line is 246), nor the
   `ParallelExecutionDomain` ordinals (`Parent=0`, `Process=2`, correct).
5. **Not a symbol collision.** No `co-compiled definitions` warning is emitted on
   the failing run, and the two transfer modules share no top-level names.

## The actual trigger, isolated to one import

`decode_process_transfer_text_line(line, ParallelExecutionDomain.Parent)` returns
`ok=true` from a probe module. Adding **one** import to that otherwise identical
probe —

```
use std.common.structural.transfer.process_frame_auth.{decode_process_transfer_authenticated_text_line}
```

— flips the same call to `ok=false, reason=invalid-process-frame`. That import
pulls in `std.common.crypto.hmac`, which drags in `std.common.crypto.types`,
which the seed cannot resolve:

```
[jit-fallback] HIR lowering error: Module resolution error:
Semantic("stdlib import `std.common.crypto.types` resolves from the project stdlib
roots only"): whole module dropped to the interpreter
```

So the import is not the defect; it is the switch that moves the program from the
JIT onto the interpreter. `src/lib/nogc_async_mut/parent_commit_piped_process.spl`
imports `process_frame_auth` unconditionally (line 12), so every user of the
piped parent-commit transport takes that fallback.

## Root cause, pinned

Under the interpreter, with everything else held fixed:

| what was decoded | result |
|---|---|
| `decode_process_transfer_frame(encode_process_transfer_frame(frame), Parent)` | `ok=true` |
| `decode_process_transfer_frame(<hand hex-decoded bytes>, Parent)` | `ok=false reason=invalid-envelope` |

and the two byte arrays are **provably equal**: same length (120), and an
element-by-element `wire[j] != expected[j]` comparison over all 120 elements
reports `mismatches=0`.

The hand-decoded array is built exactly the way the codec builds it
(`process_frame_codec.spl:131`):

```
wire.push((hi * 16 + lo) as u8)
```

So an `[u8]` whose elements come from `(<i64 expr>) as u8` compares equal
element-wise to an `[u8]` produced by the encoder, yet `decode_transfer_envelope`
(via `wire_get_u64`, `src/lib/common/structural/wire.spl`) reads different values
out of it. The elements' runtime representation differs (an i64-tagged value
where a real `u8` is expected), and the bit-assembling read path is sensitive to
that while `==` is not. This is an interpreter-path defect in `as u8` array
element representation, not a defect in any `.spl` under `src/lib`.

## Reproduction

Probes are in this session's scratchpad and are two dozen lines each:
`probe_decode.spl` (passes, JIT), `probe_decode_auth.spl` (same file + the one
import, fails), `probe_interp.spl` (encode→decode round trip under the
interpreter: passes), `probe_hex.spl` (hand hex-decode under the interpreter:
`mismatches=0`, `frame_ok=false reason=invalid-envelope`).

## Why it was not fixed here

The fix is in the seed's interpreter (`[u8]` element representation for `as u8`,
or `wire_get_u64`'s read of such elements) — the runtime-hardening lane is
forbidden from changing the Rust seed, and no `src/lib/**` change can make a
correct codec correct twice. Two secondary defects surfaced and are worth their
own attention:

- `std.common.crypto.types` is unresolvable to the seed's HIR lowering
  ("resolves from the project stdlib roots only"), which is what forces the
  interpreter fallback in the first place. Fixing that alone would put this path
  back on the JIT and make the acceptance example pass — without fixing the
  underlying `as u8` divergence, which would stay latent.
- A JIT/interpreter divergence that silently changes *results* (not just speed)
  makes `[jit-fallback]` a correctness event, not a performance note. It is
  currently logged as "expect ~100-1000x slowdown".
