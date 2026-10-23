# Struct copy-in accepts a hash-shaped word as a heap pointer and dereferences it

- **Date:** 2026-10-23 (title and attribution corrected 2026-10-24)
- **Status:** OPEN — defect is in OUR codegen, in
  `emit_aggregate_block_copy` (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`)
- **NOT a Cranelift defect.** This record was originally filed as a backend
  `cmovcc (mem),reg` soundness bug. That was wrong and the retraction is in
  "CORRECTION 2026-10-24" below; the title and status are corrected here so
  anyone triaging by header is not misdirected. Cranelift lowers our IR
  faithfully: the load is unconditional in the IR we emit, `MemFlags::new()` is
  trapping, and nothing is marked `notrap`.
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

## 2026-10-24: do NOT fix this with an address-range check (attempted, withdrawn)

I attempted the obvious fix — require the untagged word to be a canonical
user-space address — and **withdrew it** (PR closed unmerged) because review
showed it would be actively harmful. Recording it so it is not retried.

```rust
// attempted, WRONG:
let addr_limit   = iconst(I64, 1i64 << 48);
let src_in_range = icmp(UnsignedLessThan, src_ptr, addr_limit);
let src_is_valid = band(band(src_is_heap, src_nonnull), src_in_range);
```

It does stop the crash (measured: `status=CRASH exit=-139` -> `CRASH count=0`),
but **this same codegen path builds SimpleOS**, via
`--backend cranelift --target x86_64-unknown-none` from `scripts/os/*.shs`. The
kernel links higher-half (`src/os/kernel/arch/x86_64/linker.ld:32`,
`0xFFFFFFFF80000000`; aarch64 at `0xffff8000…`) and its freestanding `rt_alloc`
is a bump allocator over a `static char _heap[]` in `.bss`, so **every kernel
heap pointer is >= 2^48**. The range check marks all of them invalid, and the
pre-existing line

```rust
select(src_is_valid, tagged_new_ptr, src_tagged)   // ~:752
```

then returns the **original handle**. So in kernel code `var b = a; b.x = 1`
would mutate `a`: value semantics silently lost across the whole kernel, with no
crash and no diagnostic. Strictly worse than the SIGSEGV, because the SIGSEGV is
loud.

A residual hole defeats any range heuristic anyway: the inline-box word is
`hash << 32`, which is below 2^48 whenever `hash < 2^16`, so one unlucky variant
name would still dereference — permanently, with nothing pointing here.

### Also corrected: the invalid path does not zero-fill the result

An earlier note of mine said refusing the pointer "yields an ALL-ZERO struct".
It does not. The zero-filled block written at ~:716-718 is **never returned** —
:752 hands back the original handle and the fresh allocation is leaked. So the
`E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown>` observed after the
attempted fix is a consumer tripping over a passed-through garbage handle, not a
fail-closed guard. I mis-read the control flow of the function I was patching.

### The direction that should work

An exact predicate already exists and is used by the field accessors on these
same objects: `rt_struct_receiver_valid` (`src/runtime/runtime_native.c:7538`,
`runtime_memory.c:540`), a registry lookup over `rt_struct_allocs`. It is
target-agnostic, rejects a hash-shaped word, accepts kernel-half pointers, and
**traps with a message** instead of silently selecting — which also matches the
repo's own precedent for this class (`codegen/instr/fields.rs:21-27` does
`brif` -> `rt_eprintln_str` -> `trap`).

As it stands, copy-in uses a weaker and *different* predicate than
`compile_field_get`/`field_set` on the same object, so a struct can pass copy-in
and then trap on its first field read.

Two things to settle first, neither verified here:

1. are `rt_alloc`-made blocks registered in `rt_struct_allocs`?
   `runtime_native.c:7510` appears to register only the guarded path;
2. is a runtime call acceptable in the copy-in prologue, and if not, what is the
   cost argument against it?

### One premise still unlocated

The `hash(variant) << 32 | 1` shape is quoted from `codec_gen.spl:537`'s comment
and from this record — both written from the same crash. No inline-enum encoder
of that shape was found in the Rust runtime (`rt_enum_new` heap-allocates via
`rt_alloc`), in the Cranelift codegen, or in `src/compiler/**/*.spl`. The
measured `0xf198715900000000` is consistent with it but also with other
upper-word-only shapes. **Locating the actual producer is the prerequisite for
any calibrated fix** — that is now the top open question, ahead of the guard
itself.

## 2026-10-24 (later): the recorded next step is WRONG as written — and this is why

The section above proposed routing copy-in through `rt_struct_receiver_valid`
and listed "are `rt_alloc`-made blocks registered in `rt_struct_allocs`?" as an
unverified prerequisite. **It is now verified, and the answer kills that plan in
its current form.**

```c
void* rt_struct_alloc(int64_t size) {           // runtime_native.c:7528
    void* ptr = rt_alloc(size);
    if (ptr && !rt_struct_alloc_register(ptr, (size_t)size)) { ... }
    return ptr;
}
```

`rt_struct_alloc_register` has exactly **one** call site — that one. `rt_alloc`
itself registers into a different registry (`rt_core_transient_raw_register`),
not `rt_struct_allocs`.

And `emit_aggregate_block_copy` allocates with plain `rt_alloc`
(`closures_structs.rs:588` and `:701`), never `rt_struct_alloc`. So **structs
produced by the copy-in path are never in the registry**, and
`rt_struct_receiver_valid` returns 0 for them (it fails closed on a miss).

Dropping that predicate into copy-in as-is would therefore reject legitimate
copies — the *same* silent-breakage class as the withdrawn `1 << 48` attempt,
arrived at from the opposite direction. Anyone implementing the previous
section's advice literally would reintroduce the bug it was written to avoid.

### The actual path, in two parts

1. **Make copy-in register what it allocates**: switch `:588` / `:701` from
   `rt_alloc` to `rt_struct_alloc` so copied blocks enter `rt_struct_allocs`.
   This is also a correctness improvement on its own terms, independent of the
   guard: the field accessors already validate against that registry, so today a
   copy-in product passes copy-in and can then fail
   `rt_struct_receiver_valid` on its first field read — the asymmetry already
   flagged in review.
2. **Then** replace the tag-only predicate with `rt_struct_receiver_valid`,
   which is target-agnostic (accepts kernel-half pointers, so it does not
   repeat the `1 << 48` mistake), rejects a hash-shaped word, and **traps with a
   message** rather than silently selecting — matching the repo's precedent at
   `codegen/instr/fields.rs:21-27` (`brif` -> `rt_eprintln_str` -> `trap`).

Order matters: part 2 without part 1 is the failure described above.

### Still unlocated, and still the gating question

The producer of the offending word remains unidentified. Note that the measured
`0xf198715900000000` is `0xf1987159 << 32` with **zero** low 32 bits, which
matches an object HEADER layout (`type | size << 32`, cf.
`codegen/instr/fam_abi_tests.rs:38`) just as well as it matches a variant hash.
So even the "inline enum box" framing is not established — the word could be a
header read as a pointer.

Until the producer is found, any guard here is treating a symptom. Suggested
cheapest next move: an env-gated diagnostic in the copy-in rejection path that
prints the offending tagged word and the enclosing type name, so one stage-2 run
names the producer instead of another round of inference.

## 2026-10-24 (final): the registry predicate is NOT LINKABLE from the seed

Second correction to the fix path above, and this one is a hard constraint
rather than an ordering problem.

`src/compiler_rust/compiler/src/codegen/instr/fields.rs` carries a committed
block explaining that **`rt_struct_receiver_valid` lives only in
`runtime_native.c`, a translation unit the seed crate cannot link** (duplicate
`rt_host_gpu_*` symbols) — which is why the field-receiver guard there is
disabled by default behind `SIMPLE_SEED_FIELD_GUARD`.

So routing `emit_aggregate_block_copy` through that predicate is not available
in the lane that builds Stage 2 at all. The two-part plan recorded above
(register with `rt_struct_alloc`, then validate) is still correctly *ordered*,
but part 2 cannot be implemented until the symbol is seed-linkable.

That also explains why this predicate is a tag heuristic in the first place: the
authoritative check is unreachable from this crate. A sound fix needs either the
seed-linkable symbol (the "guard lane" that comment refers to, not yet landed)
or a target-agnostic predicate requiring no runtime call — and the obvious
candidate there, an address range, is already recorded above as harmful because
SimpleOS links higher-half.

Filed separately with its provenance:
`doc/08_tracking/bug/seed_field_receiver_guard_neutralized_and_predicate_unlinkable_2026-10-24.md`.
