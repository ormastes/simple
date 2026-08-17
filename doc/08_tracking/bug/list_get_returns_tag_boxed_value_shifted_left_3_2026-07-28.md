# `list.get(i)` returns the raw tag-boxed word (`value << 3`) on the JIT/native path

- **Filed:** 2026-07-28
- **Severity:** P0 — silent wrong values, no error, on the DEFAULT engine
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  re-verified 2026-08-07 and again 2026-08-09 — see *Re-verification* entries
  below. Root cause confirmed 2026-08-09: a missing tag-box **decode/unbox**
  step on `.get()`'s call site (the "value-vs-address" hypothesis was checked
  and refuted — `rt_array_get` takes an index and returns a tagged *value*,
  there is no byte-offset/pointer arithmetic involved). **AOT/native-codegen
  lane (`native-build --backend cranelift/llvm`) still NOT directly
  re-verified end-to-end** — three attempts 2026-08-09 were all blocked
  before reaching `.get()` codegen by a separate, already-tracked pipeline
  gap (Task #145, see 2026-08-09 entry). Structural evidence (no
  backend-conditional branching around the decode step) strongly implies the
  fix already covers AOT too, but that is inference, not a direct run. Do
  **not** read this doc as blanket-closed for the native lane.
- **Affects:** every `list.get(i)` call site returning an integer. Index read `a[i]` is CORRECT.
- **`src/os/crypto/**` `mut`-annotation prohibition (see *Blast radius* below):
  STILL STANDS.** It was written against the JIT lane specifically
  (`bin/simple run` demoting via W1006), which is now confirmed fixed — but
  since the native/AOT lane is unverified and the crypto code is
  correctness-critical, do not lift the prohibition without re-checking that
  lane too.

## Re-verification 2026-08-09 — root cause confirmed (tag-box, not addr/deref); AOT lane still unreachable, but blocker is now identified

Re-ran the JIT-lane repro again (`bin/simple run` on the exact 2026-07-28
fixture plus a fresh `[10,20,30]`/bracket-assign/`.push()`/`.first()`/
`.last()`/OOB-miss probe) — all correct, matching the 2026-08-07 table
below (`xs[1]=99 xs.get(1)=99`, `ys.get(2)=3` after 3 pushes, `ys.get(50) ??
-1 = -1`). `Array` has no `.set()` method at all (`Runtime error: Function
'Array.set' not found`) — an unrelated, pre-existing API gap, not a
regression of this bug; bracket-assign (`xs[1]=99`) is the only mutate path
and it is correct.

**Root-cause hypothesis check (address/pointer-vs-deref conflation): REFUTED.**
Read `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` in
full around the `.get()`/`.map()`/element-decode lowering (~lines 3230-3900).
The lowering is: emit a runtime call (`rt_array_get` et al.) that returns a
**tagged word** (`elem_tagged`), then call `self.decode_runtime_value(elem_tagged,
elem_type)` to untag/unbox it into the real scalar (`elem_raw`/`elem_decoded`).
This is a **tag-box decode step**, not a pointer computation — there is no
`base + i*8` address arithmetic anywhere in this path; `rt_array_get` already
takes the element *index*, not a byte offset, and returns a *value* (tagged),
not an address. The historical `<<3` factor is the tag-box's own encoding
shift (consistent with `128 << 3 = 1024` and `5 << 3 = 40` in the original
filing), not a missing dereference of an 8-byte-stride element address. The
bug was: `.get()`'s call site was missing the `decode_runtime_value` step that
`a[i]` (index-read) already applied — a missing *unbox*, not a missing
*deref*.

**AOT/native-codegen lane: still not directly executed end-to-end, but the
blocker is now pinned down and is provably unrelated to this bug.** Three
`bin/simple native-build --backend cranelift` attempts today (isolated
`/tmp` fixture + `--source src/lib`, both `--mode one-binary` and default
`dynload`) all failed identically, before reaching codegen, with:

```
[mir-lower] WARNING: unresolved method call 'get' lowered to const-0 placeholder (silent-null risk, Task #145)
[ERROR] MIR error: MIR lowering error: unresolved method call: get
error: native-build worker exited with code 1.
```

This is the **generic fail-closed "unresolved method call" guard**
(`method_calls_literals.spl` ~line 2935, `self.error("unresolved method
call: {method}", nil)` + `rt_panic` placeholder), already tracked as Task
#145 / `doc/08_tracking/bug/native_mir_lowering_unresolved_to_u8_and_join_2026-08-08.md`.
It fires whenever the receiver's runtime-array-ness can't be statically
resolved from an isolated/minimal `--source` set outside the full compiler+
app+lib source graph — it is not specific to `.get()` (the same guard also
covers `.join()`, `.char_at()`, `.slice()`, `.merge()`) and it is not the
`<<3` shift bug this doc tracks. This matches the 2026-08-07 entry's own
note that "a `native-build` attempt this session failed for an unrelated
pipeline reason before reaching the probe."

**Structural argument that the fix is backend-agnostic (why AOT is very
likely already fixed too, pending an unblocked native-build run):** grepped
every call site of `decode_runtime_value`/`box_runtime_value` around list
`.get`/`.set`-equivalent/`[i]`/`.push`/`.map`/`.first`/`.last` lowering in
`method_calls_literals.spl` and `expr_dispatch.spl`, and the LLVM backend
(`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`) for any
backend-conditional branching (`self.backend ==`, `is_jit`, etc.) around
this decode step — **none exists**. The untag/unbox call happens once, at
MIR-construction time, before any backend (cranelift-JIT, cranelift
native-object, or LLVM) ever sees the instruction stream; there is no
separate un-decoded code path reserved for AOT codegen. Given that, a
backend-specific regression limited to just the native/AOT lane would
require a *second*, independent bug in a currently-unidentified
backend-specific lowering step — nothing found supports that. This doc
should be read as: interpreter + JIT lane **directly verified fixed**
(2026-08-07 and again 2026-08-09); AOT/native lane **structurally implied
fixed** by the shared-MIR argument above, but still **not directly executed
end-to-end** because of the separate Task #145 gap. Do not close this doc's
AOT caveat until a native-build run actually reaches and exercises
`.get()` codegen.

## Re-verification 2026-08-07 — the `<< 3` shift defect is FIXED (JIT + interpreter lanes)

Re-ran the exact repro from this doc's *Symptom* section byte-for-byte,
plus a fresh minimal probe (`val xs=[10,20,30]; xs.get(1)`, `xs.get(9)`,
`xs.get(9) ?? -1`), under both engines via `bin/simple run`. Binary used:
`bin/release/x86_64-unknown-linux-gnu/simple` (the Rust seed — it prints the
"bootstrap seed only" banner; this is the same lane the 2026-07-28 filing
itself used, so the A/B is apples-to-apples, but results below are
attributed to the seed's Cranelift JIT, not the pure-Simple self-hosted
binary, which was not separately re-checked this session):

| expr | JIT (default, confirmed real via `cranelift_jit::backend` log lines) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `a.get(0)` on `[5, 7]` | `5` (was `40`) | `5` |
| `a.get(1)` after `a[1]=9` | `9` (was `72`) | `9` |
| `b.get(0)` after `push(42)` | `42` (was `336`) | `42` |
| `xs.get(1)` on `[10,20,30]` | `20`, matches `xs[1]` | `20`, matches `xs[1]` |
| `xs.get(9) ?? -1` (miss, default) | `-1` | `-1` |

The hit-path `value << 3` corruption reported above no longer reproduces on
either engine. Exact landing commit not pinned (not a dedicated "list.get
shift" commit in recent `git log` on `expr_dispatch.spl`/
`method_calls_literals.spl`); most likely folded into the runtime-array
element decode/registration hardening documented inline at
`expr_dispatch.spl` lines ~1590-1652 (`elem_struct_name`/
`elem_is_runtime_array` gating around `decode_runtime_value`) alongside the
`Array.first()`/`.last()` MIR-lowering fixes (`c49bb5606de`,
`1692ceb0b9a`) landed since this doc was filed.

**Residual, narrower, separate defect found while re-verifying:** printing a
list-get MISS directly (no `??`) — `print("{xs.get(9)}")` — renders the raw
`RT_NIL` sentinel `3` as text under the JIT (`miss=3`), while the interpreter
correctly renders `miss=nil`. The `??` operator itself is unaffected on
either engine (`-1` both lanes) — this is an Option-to-text formatting gap
for a bare list-get miss under native codegen, not the `<<3` shift this doc
tracks. Sibling check: bare out-of-bounds indexing (`xs[9]`, no `.get`) under
the JIT also silently prints `3` instead of panicking/erroring — same raw
`RT_NIL` sentinel leak, so this looks shared with the index-read path, not
`.get()`-specific. Filed as its own doc:
`doc/08_tracking/bug/jit_array_oob_read_leaks_raw_rt_nil_sentinel_2026-08-07.md`
— not chased further here since it's out of scope for this doc's original
symptom.

Regression spec added: `test/01_unit/std/improved/list_get_hit_miss_spec.spl`
(`Results: 4 total, 4 passed, 0 failed` under `bin/simple test`, which runs
the interpreter lane only — see caveat in that spec's docstring; the JIT lane
this doc is actually about still needs manual `bin/simple run` reconfirmation
after any future MIR lowering change in this area).

## Original filing (2026-07-28) — kept for history

## Symptom

`xs.get(i)` returns the value multiplied by 8 — the untagged/unshifted box word —
while `xs[i]` on the same element returns the correct value. There is no warning,
no error, and no fallback log. The program simply computes wrong numbers.

```simple
fn main():
    var a = [5, 7]
    print "a[0]={a[0]} a.get(0)={a.get(0)}"       # a[0]=5 a.get(0)=40
    a[1] = 9
    print "a[1]={a[1]} a.get(1)={a.get(1)}"       # a[1]=9 a.get(1)=72
    var b = []
    b.push(42)
    print "b[0]={b[0]} b.get(0)={b.get(0)}"       # b[0]=42 b.get(0)=336
```

Not scoped to a receiver kind or a call site: a local in `main`, a local in a
normal `fn`, and a `list` parameter all reproduce identically. Literal lists,
stored-into lists, and pushed-into lists all reproduce. The factor is exactly 8
(`<< 3`), the tag-box shift.

## Which engine

Byte-identical source, same binary:

| engine | `a.get(0)` on `[5]` |
|---|---|
| JIT / native (default) | **40** — WRONG |
| tree-walk interpreter | 5 — correct |

The interpreter row was obtained by forcing a fallback (adding a function that
trips W1006 `mutation without mut capability`, which demotes the whole program).
**`SIMPLE_NO_JIT=1` does NOT reach the interpreter** — see the companion defect
below; with that env var set the same file still prints 40.

## Companion defect: engine selection was fail-open — RESOLVED `b7151d94114`

`SIMPLE_NO_JIT=1` never selected an engine; it only moved the interpreter's
internal JIT threshold, and the Rust seed has no reader for it at all. So
`SIMPLE_NO_JIT=1 bin/simple run` prints the JIT's `40`. Likewise `--interpret`
/ `--no-jit` were discarded and `bin/simple-interp` set nothing.

**The knob that works is `SIMPLE_EXECUTION_MODE=interpret`.** An unrecognized
value silently falls through to JIT (`exec_core.rs:41 _ => ExecutionMode::Jit`),
so a typo reads as a successful interpreter run. Verified truth table:

| invocation | `a.get(0)` on `[5]` |
|---|---|
| default | 40 (JIT) |
| `SIMPLE_EXECUTION_MODE=interpret` | 5 (interpreter) |
| `SIMPLE_EXECUTION_MODE=interpreter` | 5 |
| `SIMPLE_EXECUTION_MODE=typo_xyz` | 40 — fails open |
| `SIMPLE_NO_JIT=1` | 40 — no-op on the seed |

Fixed in `b7151d94114` (synonym accepted, `SIMPLE_NO_JIT`/`--no-jit` mapped to
force-interpret, unrecognized values warn, wrapper exports the variable); the
seed keeps ignoring `SIMPLE_NO_JIT` until the next bootstrap. Guide:
`doc/07_guide/runtime/execution_engine_selection.md`. **Any past "reproduced
under both engines" claim resting on `SIMPLE_NO_JIT` proved nothing.**

## Blast radius

5,116 `.get(` call sites across 696 owned `.spl` files (excluding vendored trees).
Not all are list receivers — `Dict.get` is a separate, separately-broken API — but
the integer-list users are the dangerous ones. Concentrations, all byte-array code:

- `src/os/crypto/sm3.spl` (54), `src/lib/common/crypto/sha256_simd.spl` (49),
  `src/lib/common/crypto/sha1.spl` (44), `src/lib/common/jwt/sign.spl` (43)
- `src/os/crypto/bip39.spl` — `_set_bit` reads `old_byte = bytes.get(byte_idx)`

### BIP-39 concrete impact

`_set_bit` is currently *accidentally* correct: `src/os/crypto/bip39.spl:87`
mutates without a `mut` capability, which trips W1006 and demotes the entire
program to the interpreter, where `.get()` is right. Remove that demotion — for
example by "fixing" the warning with a `mut` annotation — and entropy→mnemonic
encoding silently corrupts on the second bit set into any byte:

    old_byte = get(0) = 128 << 3 = 1024;  1024 | 64 = 1088  (expect 192)

That is unrecoverable-wallet territory. **Do not add `mut` to any
`src/os/crypto/**` function until this is fixed.** The demotion is the safe state.
91 functions in `src/os/crypto` alone have the same W1006 shape (ChaCha20
`_quarter_round`, `poly1305_init`, `p256._sc_be_store_u64`, `curve448._x448_store28`,
`camellia._wr64`, `paseto._p4_qr`, …).

## Root cause (to confirm)

`list.get` returns the boxed slot word without applying the unbox shift that the
index-read path (`a[i]`) applies. Fix belongs in the compiler / runtime lowering
of the `get` method on list, NOT in a sweep of 5,116 call sites.

## Not the cause

The `mut` parameter annotation is innocent. A first investigation concluded
"adding `mut` corrupts output ×8"; that was a probe artifact — the probe read
results back through `.get()`. With the store verified through `a[i]`, the
`mut` and non-`mut` stores are both correct (1/3/16/100 stored, 1/3/16/100 read).

## Repro files

`~/.claude/jobs/4403a7d8/tmp/{getbug,scope,scope_demoted,min_cmp}.spl`

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — `Dict.get()`/`Dict.len()` are
  separately broken under native codegen. The two defects are independent; both
  make `.get()` unsafe.
