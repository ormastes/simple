# Struct copy-in dereferences an inline `Some` box as a heap handle

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

## RESOLVED 2026-10-24: the producer is located, and it is not a hash

Everything above treats `0xf198715900000000` as an unidentified "hash-shaped"
word and the producer as unknown. **It is identified, exactly, with no
inference left.** The word is not a hash standing on its own, and it is not a
wild pointer: it is **interior word 1 of a live, well-formed heap
`RuntimeEnum`** holding `Option::Some`.

### The arithmetic

`RuntimeEnum` (`src/compiler_rust/runtime/src/value/objects.rs:76`, `#[repr(C)]`):

| word | contents |
|---|---|
| 0 | `header: HeapHeader` — `object_type` u8, `gc_flags` u8, `reserved` u16, `size` u32 (`value/heap.rs:57`) |
| 1 | `enum_id: u32` then `discriminant: u32` |
| 2 | `payload: RuntimeValue` |

Word 1 little-endian is therefore `enum_id | (discriminant << 32)`. For an
`Option`:

- `OPTION_ENUM_ID = 1` (`objects.rs:363`)
- `discriminant = hash_variant_discriminant("Some") = 0xf1987159` (`objects.rs:354`)

```
word1        = (0xf1987159 << 32) | 1 = 0xF198715900000001
word1 & ~7   =                         0xF198715900000000   <-- the faulting address
```

That is the value in `%rsi` at the SIGSEGV, and the same value
`src/app/compiler_schema/codec_gen.spl:541` already records for
`hc_enc_hir_type`. Both reduce to the same object.

### `0xf1987159` is confirmed twice in-tree, once executably

- `src/plugins/backend_llvm_lib/llvm_lib_translate_expr.spl:622` —
  `if _sffi_enum_discriminant<LocalId>(raw_dest) == 0xf1987159:  # hash("Some")`
- `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs:8075` —
  `if ((uint32_t)rt_enum_discriminant(some) != 4053299545u) return 96;`

`0xf1987159 == 4053299545`, so the comment and the assertion name the same
constant. The second is a test, so this is not two copies of one guess.

### What the defect actually is

`emit_aggregate_block_copy` is handed a **heap `RuntimeEnum`** while applying a
**declared-struct descriptor**. Its `deep_fields` loop reads word 1 of the
block, tests `word & 7 == 1`, and treats the result as a nested handle.

The collision that turns the type confusion into a fault is numeric and exact:

```
OPTION_ENUM_ID    = 1
RT_VALUE_TAG_HEAP = 1
```

Word 1 of EVERY `Option` object therefore passes the handle test — low bits `1`,
untagged part nonzero — no matter which variant it holds. The copy then
dereferences `discriminant << 32`.

### The descriptor is not at fault

`struct_deep_fields` (`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1060`)
emits a field descriptor only when all of these hold: the field type name
resolves, `type_value_kinds[name] == Some(true)` (declared `struct`), and
`registry.get(fty)` is a non-empty `HirType::Struct`. An enum-typed field gets
no descriptor. So the descriptor correctly describes its declared type — the
**value reaching the slot is the wrong kind of object**. This is a type
confusion upstream of codegen, not a bad descriptor and not a bad guard.

### Why all three previously attempted fixes were wrong

Each failed for its own reason, and each reason is now explained by the above:

1. **Narrow `src_is_valid`** (PR #4239, withdrawn as P0). Cannot work: the tail
   of the function returns `src_tagged` unchanged when invalid, so rejecting the
   word silently aliases instead of copying — `var b = a; b.x = 1` mutates `a`.
   The `1 << 48` form additionally rejects every SimpleOS higher-half pointer.
2. **A registry-membership probe.** Cannot work here: AOT lowering allocates
   Simple structs as raw `rt_alloc` blocks that are never registered
   (`src/runtime/runtime_native.c:10296` records this and the resulting
   "unregistered HirModule node", `stores=0 refused=1351`). A registry probe
   rejects every struct.
3. **`rt_heap_ref_wellformed`** (the generated-visitor guards, abandoned). Cannot
   work: it is `(value & ~TAG_MASK) >= 4096`, and `runtime_native.c:10288` states
   outright that "any large garbage integer passes it". `0xf198715900000000`
   passes, so those guards were inert, not merely weak.

### Where a fix belongs

Not in `emit_aggregate_block_copy`. The word it dereferences is a correct word
of a correct object; the error is that an `Option` value is in a slot the
descriptor says is a struct. Two candidate owners, both upstream:

- **Lowering** — stop an `Option`-typed value from reaching a struct-typed slot
  (the codec's optional handling is the suspected path: `HirExpr` optional
  payloads, and `Assign(op: HirAssignOp?)` at `hir_definitions.spl:801`).
- **Representation** — make `OPTION_ENUM_ID` not collide with
  `RT_VALUE_TAG_HEAP`. The collision is what converts a detectable type
  confusion into a silent dereference, and it will keep producing
  "the nil guard does not work" reports until it is broken.

The second is the smaller change and would make this class of confusion
*detectable* everywhere at once rather than fixing one path.

### Diagnostic

`emit_aggregate_block_copy` carries an env-gated probe
(`SIMPLE_AGGREGATE_COPY_DIAG`, codegen-time) that prints the enclosing type name
before the existing fault. It emits nothing when unset, so every release and
bootstrap artifact is byte-identical. It is retained to name the enclosing type
of the next instance of this class without another 50-minute bootstrap.

## CORRECTION 2026-10-24 (same day): this was already documented in-tree

The section above says the producer was "unlocated" and presents the
`RuntimeEnum` word-1 derivation as new. **Both claims need correcting, and the
correction matters more than the derivation.**

`src/app/compiler_schema/codec_gen.spl` (the `_emit_dec` node/opaque branch)
already carries this explanation, with the exact value and the exact slot:

> Bug (selfhost_hir_cache_encode_hir_type_segv_2026-08-22): the if-EXPRESSION
> form unifies both arms at `T?`, so the taken arm is boxed as an inline `Some`
> enum word (hash("Some")<<32 | 1). Stored into a NON-optional field --
> HirType.span is declared `span: Span` -- that enum word is then deep-copied as
> a tagged `Span` pointer by the next callee's value-semantics copy-in prologue,
> faulting on 0xf198715900000000 in hc_enc_hir_type.

So the `hash(variant) << 32 | 1` premise recorded elsewhere as "unlocated in any
producer" was never unlocated. It is stated in a file this lane had already
edited (PRs #4232, #4233), and reading it first would have saved the whole
search.

### Two bit-identical mechanisms; the value cannot distinguish them

| mechanism | word |
|---|---|
| inline `Some` box (what `codec_gen.spl` asserts) | `hash("Some") << 32 \| 1` |
| heap `RuntimeEnum` word 1 (the derivation above) | `enum_id \| (discriminant << 32)` = `1 \| (hash("Some") << 32)` |

Both are `0xF198715900000001`, so `%rsi = 0xF198715900000000` is consistent with
either and **proves neither**. The record above overstated it by presenting the
second as established. `codec_gen.spl`'s attribution is the better supported of
the two, because it names a concrete construction site.

### The generator's node/opaque mitigation is already applied

`_emit_dec` emits the statement form, not the if-expression:

```simple
var f_type_: HirType? = nil
if r.next_i64() == 1:
    f_type_ = hc_dec_hir_type(r)
```

Per that comment the statement form "assigns the bare value without boxing", so
`f_type_` holds a bare node, and when the field is absent it stays `nil` — whose
immediate is **3**, giving tag 3, which the copy-in's `tag == 1` test correctly
rejects. **So the decoder path is mitigated and is not the open hole.** An
earlier draft of this record claimed the decoder was the root cause because
`f_type_` is *declared* `HirType?` while `HirExpr.type_`
(`hir_definitions.spl:561`) is non-optional. The declaration is not the
representation here; that claim is withdrawn.

### What does survive from the derivation

Four things, none of which the in-tree comment states:

1. **`0xf1987159` is `hash_variant_discriminant("Some")`, confirmed twice and
   once executably** — `llvm_lib_translate_expr.spl:622` comments it, and
   `native_project/tests.rs:8075` asserts
   `rt_enum_discriminant(some) == 4053299545`, the same number. The generator's
   comment asserts the shape without citing provenance.
2. **The collision is numeric and total: `OPTION_ENUM_ID == RT_VALUE_TAG_HEAP == 1`**
   (`objects.rs:363`). This is why an `Option` — inline box *or* heap word 1 —
   passes `src_is_valid` regardless of variant. It generalises: any enum id
   whose low 3 bits are 1 collides. Documented nowhere.
3. **The descriptor is not at fault.** `struct_deep_fields`
   (`mir/lower/lowering_core.rs:1060`) emits a field descriptor only for a
   declared `struct` with a non-empty `HirType::Struct` field list, so an
   enum-typed field gets none. `struct HirType` has `span: Span` at field index
   **1** (`hir_types.spl:662`), which is why the descriptor reads word 1 — the
   same slot `runtime_native.c:10288` independently records as a "wild
   HirSymbol span".
4. **Why all three attempted fixes failed**, each for its own reason (table
   above).

### Net

The open hole is NOT the decoder. It is that **some remaining construction site
still stores an inline `Some` box into a non-optional node field**, and the
copy-in cannot tell it from a handle because of collision (2). Finding that site
is what the `SIMPLE_AGGREGATE_COPY_DIAG` probe is for; `codec_gen.spl`'s note
says the scalar case was "already hit once and fixed by inlining" and that the
node/opaque case was "left unmitigated" until the statement form, so a third
category is the place to look.

## MEASURED 2026-10-24: it IS a heap `RuntimeEnum`, carrying `Some(NULL)`

Everything above this line was reasoning from a single address. This section is
a direct measurement of the faulting object under gdb, and it settles the
question the section above said could not be settled.

### Reproduction — ~200 ms, and it dumps core

```sh
R=.simple/storage/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple.rejected
M=src/compiler/bootstrap_admission/stage2_module_path_naming.spl
CAP_MEM_MAX=4G sh scripts/resource/run_capped.shs "$R" native-build "$M" -o /tmp/out
# rc=139, "the monitored command dumped core"
```

Under gdb the worker flag is required, or the run forks and the trap is missed:

```sh
SIMPLE_NATIVE_BUILD_WORKER=1 gdb -q -batch -ex run -ex 'bt 30' \
  -ex 'info registers r8 r10 r11 r14 rax' --args "$R" native-build "$M" -o /tmp/out
```

### Backtrace

```
#0  compiler.hir.generated.hir_visitor.walk_hir_type
#1  compiler.hir.generated.hir_visitor.walk_hir_expr
#2  compiler.hir.generated.hir_visitor.walk_hir_stmt
#3  compiler.hir.generated.hir_visitor.walk_hir_block
#4  compiler.semantics.representation_boundary.unsafe_observations.representation_observe_function_v1
#5  ...representation_missing_manifest_observations_v1
#6  compiler.driver.hir_semantic_consumer_v1.collect_module_representation_receipt_v1
#7  compiler.driver.driver_hir_pipeline_passes.run_representation_manifest_pass
#8  ...lower_and_check_retained
```

### The faulting instruction is the copy-in prologue

```
767e49:  mov    %rax,%r10          ; r10 = new_ptr
767e4c:  cmovne %r8,%r10           ; load_ptr = select(src_is_valid, src_ptr, new_ptr)
767e55:  cmovne (%r10),%r11        ; <-- SIGSEGV; load fused into cmov
767e59:  mov    %r11,(%rax)
767e61:  cmovne 0x8(%r10),%rdi
767e66:  mov    %rdi,0x8(%rax)
```

`r8 = r10 = 0xf198715900000000`. Exactly **two** words are stored (`(%rax)`,
`0x8(%rax)`), so the descriptor being applied has `byte_size` 16 — and
`struct HirType` has exactly two fields, `kind` and `span`
(`hir_types.spl:662`). So frame #0 is `walk_hir_type` copying its incoming
`HirType` parameter, and frame #1 reached it through the generated
`if node.has_type_: acc = walk_hir_type<C>(node.type_, acc, f)`.

### The object, dumped

At frame #1, `r12 = 0xf198715900000001` (the tagged word) and `r13` is a tagged
pointer. Dumping `($r13 & ~7)`:

```
0x3426720:  0x0000001800000007   <- HeapHeader: object_type=7 (Enum), size=0x18 = 24
0x3426728:  0xf198715900000001   <- enum_id=1 (OPTION_ENUM_ID) | discriminant=0xf1987159 << 32
0x3426730:  0x0000000000000000   <- payload = NULL
```

That is a live, well-formed 24-byte `RuntimeEnum`
(`runtime/src/value/objects.rs:76`): header, `enum_id`/`discriminant`, payload.

**Two conclusions follow, and both correct text above:**

1. **The `RuntimeEnum` reading is confirmed; the inline-`Some`-box reading is
   not what happened here.** The section above says the observed address is
   consistent with either and proves neither — true of the address alone, but
   the header settles it. `codec_gen.spl`'s attribution ("boxed as an inline
   `Some` enum word") is correct about a mechanism that exists, but it is not
   the mechanism of *this* fault.
2. **The Option is `Some(NULL)`** — marked present with a nil payload. That is
   itself malformed and is a second defect, independent of the copy.

### Why the copy faults, in full

An `Option<HirType>` object is in a slot whose descriptor says bare `HirType`:

| step | effect |
|---|---|
| parent copy reads the slot | gets the tagged `RuntimeEnum` pointer — a genuine handle, passes every validity test legitimately |
| recursive copy applies `HirType`'s descriptor | copies **2** words from a **3**-word enum: word 0 (the header) and word 1 (`enum_id\|discriminant`) |
| `HirType`'s deep field is `span: Span` at index **1** | re-reads copied word 1 = `0xf198715900000001` |
| low 3 bits are `1` because `OPTION_ENUM_ID == RT_VALUE_TAG_HEAP == 1` | treated as a `Span` handle |
| recursive copy | `src_ptr = 0xf198715900000000`, unmapped -> **SIGSEGV** |

So the fault needs no wild pointer and no corrupt memory. Every object involved
is well formed. It needs only an `Option` in a struct-typed slot, plus the
`enum_id`/tag collision.

### Hypotheses tested and DISPROVED this round

Recording these so nobody repeats them:

- **`case Some(v)` binds the box instead of the payload.** Disproved. A probe
  (`Option<struct>` destructured, payload passed to a by-value struct parameter
  with a nested struct at field index 1) prints `PROBE OK payload-bound`,
  result correct. Caveat: tested under JIT; the native path additionally runs
  `qualify_native_struct_layouts`, so this does not clear the native path.
- **The Dict bracket-read in `run_representation_manifest_pass`**
  (`var module: HirModule = hir_modules[name]`). Disproved: the read lowers to
  `rt_dict_get` -> bare `i64` -> `decode_runtime_value`
  (`mir_lowering_stmts.spl:2382`). No `Option` is constructed, so there is no
  box to leak. (`Dict.get()` returning `T?` is a different surface.)
- **`type_: span_from` at `synth_enum.spl:77`.** Not a confusion: `span_from` is
  declared `HirType` at `:61`.
- **A raw-NULL dereference.** Briefly suspected from `rsi = 0x30`, which is
  **not** the faulting operand — the operand is `(%r10)`. `rt_heap_ref_wellformed`
  (`>= 4096`) would reject a raw NULL but passes `0xf198715900000000`, so it is
  still inert for this fault.

### The probe landed in PR #4244 is INERT in the bootstrap lane

Stated plainly because it is a defect in that change. `SIMPLE_AGGREGATE_COPY_DIAG`
never reached the process doing codegen, so the branch was never emitted:

```
strings <seed>            | grep -c 'aggregate-copy diagnostic'  -> 1
strings <stage2 candidate>| grep -c 'aggregate-copy diagnostic'  -> 0
```

The Stage 2 lane admits a **closed set of exactly three** diagnostic env names —
`SIMPLE_MEM_SNAPSHOT_FILE`, `SIMPLE_EVIDENCE_RUN_ID`, `SIMPLE_M4_WORK_RECEIPT`
(`scripts/check/lib/bootstrap-stage3/authority.shs:619`) — whose sibling comment
reads *"Never inherit diagnostics from ambient env."* So the exclusion is by
design, not a bug in the script. The probe still works on a direct
`native-build` invocation outside the script; to make it usable inside the
bootstrap it must be added to that allowlist (and to `build_env_sha256`), which
is an owner decision. The gdb measurement above obtained the same fact
(`type_name` = `HirType`) without it, by word count.

### Stage 2 status

`p2_add.spl` now **passes** — the probe that blocked this lane for days. The
failure moved to `stage2_module_path_naming.spl`:

```
[hir-cache-store] refused reason=unstable ...; entry not stored
[hir-blob-refused] RT-E-HIR-BLOB-DECODE: module blob 0 could not be decoded;
    validating the in-memory module instead (codec-class refusal is non-fatal;
    the build proceeds UNCACHED)
[WARN] any-escape pass: 0 diagnostic(s)
error: native-build worker terminated with signal 11 before producing a binary;
    NOT a compile failure.
candidate_frontend_smoke: stage2-module-path-naming-build failed (raw rc=117)
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

Note the ordering: the codec refusal is handled **gracefully** and the build
proceeds uncached; the SEGV happens afterwards, in the representation pass over
the **freshly lowered** module. So the codec is not the producer here.

### Next step

Find which fresh-lowering site stores a `Some(...)` into a non-optional
`HirType` slot while setting `has_type_ = true`. There are 59 `has_type_: true`
construction sites under `src/compiler/`; the HIR-phase ones (`10.frontend`,
`35.semantics`, `40.mono`) are reachable here, the `50.mir` ones are not.
`attach_inferred_type` (`src/compiler/35.semantics/resolve_lookup_helpers.spl:28`)
is the strongest candidate — it is the one site that takes an inferred
`HirType?` and writes it into `type_` with `has_type_: true`, and the observed
discriminant is literally `hash("Some")`. It is **not** confirmed: the
payload-binding probe above passed under JIT, so if this site is the producer
the divergence is native-only.
