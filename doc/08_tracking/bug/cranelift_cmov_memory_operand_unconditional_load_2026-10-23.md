# Backend emits `cmovcc (mem),reg`, so a nil/presence guard dereferences on the path it was meant to protect

- **Date:** 2026-10-23
- **Status:** OPEN — backend/codegen defect
- **Severity:** blocks Stage 2 admission on `release/1.0.0`, and therefore any
  full bootstrap. Also explains a family of "the nil guard does not work"
  bugs that have each been investigated separately.
- **Lane:** Linux x86_64, `--backend=cranelift`, stage-2 candidate compiler

## The instruction

`walk_hir_type` in the GENERATED HIR visitor, during
`run_representation_manifest_pass`:

```
+212: and    %r11d,%edx
+215: test   %dl,%dl
+217: mov    %rax,%rsi
+220: cmovne %r10,%rsi        # rsi := r10 on one path
+224: test   %dl,%dl
+226: mov    %rbx,%rdi
+229: cmovne (%rsi),%rdi      # <-- SIGSEGV: loads from (%rsi)
```

with

```
r10 = 0xf198715900000000      # a TAGGED word, not an address
rsi = 0xf198715900000000
rdi = 0x0
si_addr = 0x0
```

**On x86, `CMOVcc` with a memory source operand reads that memory regardless of
whether the condition is met.** So the backend folded a conditionally-selected
*dereference* into a single `cmov`, and the load from the tagged
(non-dereferenceable) word happens on BOTH paths — including the path where the
guard had already decided the value was not usable.

`0xf198715900000000` is not a new value here: `src/app/compiler_schema/codec_gen.spl`
already records it verbatim — "that enum word is then deep-copied as a tagged
`Span` pointer by the next callee's value-semantics copy-in prologue, faulting
on 0xf198715900000000 in hc_enc_hir_type". Same tagged-word class, same fault,
different function.

## Why this is the root cause of a whole family

A guard cannot protect a value whose protection compiles to an unconditional
load of that value. That is why every source-level guard tried against this
family has failed, each time looking like a different bug:

| guard form tried | where | outcome |
|---|---|---|
| `if node == nil:` | `fold_gen.spl` walk prologues | SIGSEGV persists (`== nil` compares against nil's immediate 3, never matches a raw 0/tagged word) |
| `.?` / `rt_is_some` | proposed for the same prologues | would not help: `runtime_native.c:5612-5616` treats a raw zero word as a valid PRESENT payload |
| `rt_heap_ref_wellformed(node)` | added to the walk prologues (this session) | SIGSEGV persists at the same instruction — the guard itself is inside the folded `cmov` |
| optional payload bind | `codec_gen.spl` `_emit_enc` (#4232) | fixed the CODEC instance, because it removed the typed copy-in rather than adding a test |

Note the pattern in the last row: the one fix that worked did so by **removing a
dereference**, not by adding a check. That is consistent with this diagnosis and
is the shape any further source-level mitigation has to take.

## Suggested direction

The fix belongs in the backend: never fold a conditionally-selected load into
`cmovcc (mem),reg`. Emit a branch (or a select over two already-loaded values)
so the load happens only on the path that needs it. A load whose address comes
from a `select` is only safe to hoist when BOTH candidate addresses are provably
dereferenceable, which is exactly the condition that fails here — one side is a
tagged non-pointer.

Until that lands, source-level mitigations must avoid materialising or
dereferencing the value at all on the guarded path (as #4232 did), rather than
testing it.

## Reproduction

```sh
# worker argv (-s must be large or the base64 policy arg truncates)
strace -f -qq -s 60000 -e trace=execve -o /tmp/st.log \
  .simple/storage/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple.rejected \
  native-build --runtime-bundle core-c-bootstrap --entry-closure \
  --entry src/compiler/bootstrap_admission/stage2_module_path_naming.spl -o /tmp/p
# SIMPLE_NATIVE_BUILD_WORKER=1 is required (bootstrap_main.spl:629)
env -u SIMPLE_BOOTSTRAP SIMPLE_NATIVE_BUILD_WORKER=1 gdb -q -batch \
  -ex run -ex 'x/10i $pc-28' -ex 'info registers r10 rsi rdi' --args <argv>
```

Reproduces in ~110 ms; no bootstrap needed.

## Scope note, stated rather than implied

This record identifies the faulting instruction and explains the family. It does
NOT establish which backend pass folds the select, nor whether the LLVM backend
emits the same shape (this host has no LLVM 23, so only cranelift was measured).
Both are open.

## CORRECTION 2026-10-24: this is OUR predicate, not a backend defect

The title and the "Suggested direction" above are **wrong**, and the misdiagnosis
was mine. Cranelift lowered faithfully what our IR asked for; there is no
`cmovcc (mem),reg` soundness bug to fix in the backend.

The real site is `emit_aggregate_block_copy` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`, the
value-semantics struct copy-in prologue. It emits, in this order:

```rust
let src_ptr  = band(src_tagged, !7);
let src_tag  = band(src_tagged, 7);
let src_is_heap  = icmp(Equal, src_tag, one);        // low bits == 1
let src_nonnull  = icmp(NotEqual, src_ptr, zero);
let src_is_valid = band(src_is_heap, src_nonnull);
let load_ptr = select(src_is_valid, src_ptr, new_ptr);   // -> cmovne %r10,%rsi
for w in 0..words {
    let word = load(I64, MemFlags::new(), load_ptr, off); // -> cmovne (%rsi),%rdi
    let word = select(src_is_valid, word, zero);
    store(word, new_ptr, off);
}
```

So the load IS unconditional in our own IR — the two `select`s choose the
address and then the value, and cranelift merged them into the two `cmov`s seen
in the disassembly. `MemFlags::new()` is correct (trapping); nothing is marked
notrap. The backend is not at fault.

**The defect is the validity predicate.** The heap tag (low bits `== 1`) does
not identify a heap pointer on its own: an INLINE enum box is
`hash(variant) << 32 | 1`, a shape `src/app/compiler_schema/codec_gen.spl`
already states verbatim. Its low bits collide with the tag, so `src_is_heap`
accepts it, `src_ptr` becomes the hash `0xf198715900000000`, and the word load
dereferences a hash as an address. That is exactly the `r10`/`rsi` pair in the
register dump above, and exactly the constant that file records for
`hc_enc_hir_type`.

### Fix applied, and what it does and does not do

Require the untagged word to be a canonical user-space address — one compare,
no runtime call; a real heap pointer is well below 2^48, a hash-derived word is
not:

```rust
let addr_limit  = iconst(I64, 1i64 << 48);
let src_in_range = icmp(UnsignedLessThan, src_ptr, addr_limit);
let src_is_valid = band(band(src_is_heap, src_nonnull), src_in_range);
```

Measured on the stage-2 sanity battery (Linux x86_64, cranelift):

| | result |
|---|---|
| before | `status=CRASH exit=-139`, SIGSEGV at `cmovne (%rsi),%rdi` |
| after | **`CRASH count=0`**, worker exits cleanly with code 1 |

**It does not make Stage 2 pass**, and the reason is informative. When
`src_is_valid` is false the loop stores `zero` for every word, so refusing the
bogus pointer yields an **all-zero struct** — a `HirType` whose `kind` is 0.
The battery now reports:

```
E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown> unhandled at walk_hir_type
```

i.e. a fail-closed diagnostic where there used to be a segfault. That is the
correct behaviour for this layer, and it relocates the remaining defect to the
**producer**: something stores an inline `Some` box into a non-optional
`HirType` field, so a struct copy is attempted on a value that was never a heap
struct. `codec_gen.spl` documents that exact hazard for the codec's own decoder
("the if-EXPRESSION form unifies both arms at `T?`, so the taken arm is boxed as
an inline `Some` enum word … Stored into a NON-optional field"), and the
decoder was fixed to assign bare values; some other producer in HIR lowering
still does it.

### Next step

Find the producer. The question is no longer "why does the copy crash" but
"which HIR lowering path stores an Option box into a non-optional `HirType`
field". The `<unknown>` variant report now names the consuming function
(`walk_hir_type`) on every occurrence, which is a usable starting point that did
not exist while this crashed.
