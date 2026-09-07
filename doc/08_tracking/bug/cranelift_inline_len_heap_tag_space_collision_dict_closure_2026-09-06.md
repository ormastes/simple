# Cranelift `inline_runtime_len_value` conflates two heap-tag spaces: `.len()` on a closure returns a fabricated length

- **Filed:** 2026-09-06
- **Severity:** high — silent wrong answer. `.len()`/`.is_empty()` on an untyped/ANY-erased
  closure returns a plausible non-negative integer instead of the `rt_len` contract's `-1`.
  No diagnostic, no crash.
- **Status:** OPEN — **REAL** (source-confirmed defect; runtime hit not executed, see
  "What was NOT established")
- **Component:** Rust seed, Cranelift backend —
  `src/compiler_rust/compiler/src/codegen/instr/helpers.rs`
- **Verified against:** `origin/main` @ `4699194f81e` (2026-09-06), read-only worktree.
- **Origin of the lead:** noticed while reading the neighbourhood of the still-OPEN PR #257
  (baremetal tag work). **Not** surfaced by a failing test — no test covers this.

## Verdict

| question | answer |
|---|---|
| Is the arm gated by target? | **No.** `helpers.rs:81`, no `Target`/baremetal condition anywhere in the function. |
| Does the tag collide? | **Yes**, exactly. Freestanding `RT_VALUE_HEAP_DICT = 0x06`; hosted `HeapObjectType::Closure = 0x06`. |
| Is it emitted on a hosted build? | **Yes** — the function is target-independent and its sibling tag-3 arm exists *for a hosted-only type*. |
| Is the wrong value observable? | **Yes** — offset 16 of a hosted `RuntimeClosure` is `capture_count`, explicitly zero-initialised, so the result is a clean small non-negative integer. |
| Already fixed? | **No.** PR #257 is `state: OPEN`, `mergedAt: null`. No `baremetal` field exists on `InstrContext`. |
| Is the defect one-directional? | **No** — it is **two-way**. See "The symmetric half". |
| Does gating on `is_baremetal()` fix it? | **No** — both runtimes link into one hosted binary. See "Fix shape". |

## The collision, from source

Two *different* heap-kind spaces are overlaid on the same first byte, and they
disagree on precisely dict and closure — the two are **swapped**:

| kind byte | Rust runtime — `HeapObjectType` (`runtime/src/value/heap.rs:8-16`, `#[repr(u8)]` at `:6`) | C RtCore runtime — `RT_VALUE_HEAP_*` (`src/runtime/runtime_native.c:248-253`) |
|---|---|---|
| `0x02` | `Array = 0x02` | `RT_VALUE_HEAP_ARRAY 0x02U` — agree |
| `0x03` | `Dict = 0x03` | `RT_VALUE_HEAP_CLOSURE 0x03U` — **collide** |
| `0x06` | `Closure = 0x06` | `RT_VALUE_HEAP_DICT 0x06U` — **collide** |

`inline_runtime_len_value` branches on that byte with no knowledge of which space it is in.

## The ungated arm

`src/compiler_rust/compiler/src/codegen/instr/helpers.rs:74-81`:

```rust
    // simple-core SplDict (freestanding / SimpleOS native-build) uses tag byte 6
    // with layout {tag@0, cap@8, len@16, items@32} — unlike RuntimeDict (tag 3,
    // len@8). Without this case `.len()`/`.values()` on an untyped/ANY-erased
    // dict hit the -1 sentinel here, silently under-counting iteration and
    // dropping a synthesized `main` during in-guest HIR lowering (the SimpleOS
    // interpreter then reports "module has no main function").
    let is_spldict = builder.ins().icmp_imm(IntCC::Equal, object_type, 6);
```

and `:94-101`:

```rust
    builder
        .ins()
        .brif(is_spldict, spldict_len_block, &[], other_len_block, &[]);
    builder.seal_block(len_block);

    builder.switch_to_block(spldict_len_block);
    let len16 = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 16);
```

The comment scopes the intent to "freestanding / SimpleOS native-build". **The code
does not.** The whole function takes only `builder` and `value`; it receives no
`InstrContext`, no `Target`, and reads no target state.

**Naming note (worth correcting when this is fixed):** the comment says `SplDict`,
but `SplDict` (`src/runtime/runtime.h:192-197`) is `{entries@0, cap@8, len@16,
tombstones@24}` — it carries **no tag byte at all** (`spl_dict_new` is a bare
`calloc`, `runtime_legacy_core.c:378-380`), so its byte 0 is a pointer LSB and is
never reliably 6. The struct the arm actually describes is `RtCoreDict`
(`runtime_native.c:1066-1075`): `{kind@0, flags@1, reserved@2, transient_scope_id@4,
cap@8, len@16, tombstones@24, entries@32}` — which matches "cap@8, len@16, items@32"
exactly, and whose `kind` is `RT_VALUE_HEAP_DICT 0x06U`. The arm is correct for
`RtCoreDict`; only its name and its missing gate are wrong.

## The wrong value, concretely

`src/compiler_rust/runtime/src/value/objects.rs:11-21`, `#[repr(C)]`:

```rust
pub struct RuntimeClosure {
    pub header: HeapHeader,        // 8 bytes: object_type u8, gc_flags u8, reserved u16, size u32
    pub func_ptr: *const u8,       // offset 8
    pub capture_count: u32,        // offset 16
    pub reserved: u32,             // offset 20
}
```

`HeapHeader` (`heap.rs:55-66`, `#[repr(C)]`) is `u8 + u8 + u16 + u32` = 8 bytes, so
**offset 16 is `capture_count`**. `rt_closure_new` (`objects.rs:182,190`) uses
`alloc_zeroed` and then explicitly writes `(*ptr).reserved = 0`, so the high 32 bits
of the i64 loaded at offset 16 are guaranteed zero.

**Therefore `.len()` on a hosted closure returns exactly its capture count.**
A non-capturing lambda yields `0` — and `.is_empty()` on it yields `true`.
A closure capturing two variables yields `2`. Every one of these is a valid-looking
answer, which is what makes it silent.

## Divergence from the runtime contract

The inline is a *substitute for*, not a *fast path in front of*, the runtime call.
`src/compiler_rust/compiler/src/codegen/instr/methods.rs:87-89`:

```rust
    if func_name == "rt_len" {
        return inline_runtime_len_value(builder, receiver);
    }
```

It returns unconditionally — `rt_len` is never called, so there is **no fallback that
could recover**. And the real `rt_len`
(`src/compiler_rust/runtime/src/value/collections.rs:2406-2414`) is explicit:

```rust
pub extern "C" fn rt_len(value: RuntimeValue) -> i64 {
    match value.heap_type() {
        Some(HeapObjectType::Array) => rt_array_len(value),
        Some(HeapObjectType::String) => rt_string_len(value),
        Some(HeapObjectType::Tuple) => rt_tuple_len(value),
        Some(HeapObjectType::Dict) => super::dict::rt_dict_len(value),
        _ => -1,
    }
}
```

`Closure` falls to `_ => -1`. So on one lane the same source expression yields `-1`
and on the Cranelift-inlined lane it yields `capture_count`. That divergence is the
defect: it is not "a sentinel is wrong", it is "the correct sentinel is replaced by a
fabricated length".

## Reachability — why this is REAL and not theoretical

1. **Emission is unconditional.** `inline_runtime_len_value` has no target parameter
   (`helpers.rs:43-46`). Whatever target is being compiled, all four arms are emitted.
2. **The function is a hosted code path by the codegen's own testimony.**
   `helpers.rs:70-73` adds the tag-3 arm because otherwise `d.len()` on an untyped dict
   "fall[s] through to the -1 sentinel under the Cranelift JIT fast path". `RuntimeDict`
   (tag 3, `len` at offset 8 — `dict.rs:34-42`) is a **hosted-only** Rust type. An arm
   written to fix hosted `RuntimeDict` behaviour is, by construction, in a function that
   runs on hosted builds.
3. **Six live call sites**, none target-gated:
   `closures_structs.rs:1620,1636,2161,2318`, `methods.rs:89`, `calls.rs:320`.
   The selector at `methods.rs:87` is the intrinsic name `rt_len`; the one at
   `calls.rs:317-321` (`compile_inline_len`) picks the array-only variant when
   `trusted_array` is set and this general variant otherwise — i.e. the general variant
   is precisely the *untyped-receiver* case, which is the case that can hold a closure.

## The symmetric half (same root, opposite lane)

The tag-3 `is_dict` arm is equally ungated, so it mis-fires in the other direction:
a **freestanding** `RtCoreClosure` has `kind == RT_VALUE_HEAP_CLOSURE == 0x03`, matches
`is_dict`, and takes the `other_len_block` path that loads offset 8. Per
`runtime_native.c:1045-1052` — `{kind@0, reserved[3]@1, transient_scope_id@4,
func_ptr@8, capture_count@16, captures[]@24}` — **offset 8 is `func_ptr`**. So on the
freestanding lane `.len()` on a closure returns a raw code address as a length. That is
strictly worse than the hosted half (an enormous number rather than a small plausible
one), and it is the same missing gate.

Any fix must close both directions, not just tag 6.

## Fix shape (NOT implemented here, per the filing request)

**First, a correction to the obvious-looking fix — it would cause a regression.**
The two tag spaces are *not* "hosted vs baremetal", and gating on
`Target::is_baremetal()` (`src/compiler_rust/common/src/target.rs:732`) is the wrong
discriminator. `runtime_native.c` is the general **C RtCore runtime**, not a
baremetal-only file, and it is linked into **hosted** builds. Measured from
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1624-1652`, the
Stage-2 hosted link puts the Rust `native_all` archive *and* the core-C archive on the
same command line:

```
    // Those live in runtime_native.c, which the core-C
    // archive compiles and nothing else in this build does.
    // Supply it as an ADDITIONAL archive, exactly like the
    // Stage 4 supplement above, rather than replacing
    // native_all ...
    ...
    // ~514 of which native_all defines
    // too (measured -- the same class 8ca87866c6 recorded
    // as 475 collisions).
```

So on a hosted target, ~514-560 `rt_*` symbols are defined by **both** runtimes and the
winner is decided by archive order and `/FORCE:MULTIPLE` first-wins — per symbol, at
link time. A target-triple gate cannot see that. Worse, both allocators can be live in
one process, so the tag space a given heap object belongs to is a property of *which
runtime allocated it*, not of the target being compiled.

The two runtimes do not even agree on the sentinel. Rust `rt_len`
(`collections.rs:2406-2414`) returns `-1` for an unhandled type; C `rt_len`
(`runtime_native.c:3071-3076`) returns `0`, and handles only string and array — no dict
arm at all, which is the actual reason the `is_spldict` arm was bolted into codegen in
the first place.

Fix directions, in preference order:

1. **Stop overloading the byte.** Make the two runtimes agree on the heap-kind
   numbering — the cheapest form is to move `RT_VALUE_HEAP_CLOSURE`/`RT_VALUE_HEAP_DICT`
   onto `HeapObjectType`'s `0x06`/`0x03` (array `0x02` and the string magic already
   agree, so only this pair moves). Then one table decodes both and the gate question
   disappears. This is the durable fix and it is the one worth costing.
2. **Decode defensively instead of guessing.** Before trusting an offset, validate the
   candidate — e.g. require the object's own `size`/`cap` field to be consistent with the
   length being loaded, and fall through to the `-1` sentinel when it is not. Slower, but
   it degrades to "unknown" rather than to a fabricated number.
3. **Do not** simply thread `is_baremetal()` in. Per the linker evidence above that
   would select the Rust table on hosted native-builds that are actually linked against
   RtCore, breaking dict `.len()` — trading this silent wrong answer for a different one.
   If a static gate is pursued at all, the axis must be *which runtime ABI this module is
   linked against*, which the codegen does not currently know and would have to be
   plumbed.
4. **Interim mitigation only:** delete the `is_spldict` arm and restore `-1` for tag 6.
   That re-breaks the SimpleOS in-guest `.len()` case the arm was added for
   (`28ff5e05494`, 2026-07-14) and needs its own record. Not a fix.

Note arrays and strings agree across both spaces (`0x02` is array in both; `RtCoreArray`
keeps `len` at offset 8, `runtime_native.c:1018-1026`), so only the dict/closure pair is
in scope.

## What was NOT established

- **No execution.** This session was constrained to source reading (an open memory bug
  forbids builds), so nothing here was demonstrated by running a compiled program. The
  emission, the discriminants, and the struct offsets are all read from committed source;
  the *runtime* hit is inferred from them, not observed.
- **No repro program is offered**, because reaching the bad branch needs a `.len()` on a
  value the compiler has erased to ANY/untyped that holds a closure at runtime. Such a
  program is almost certainly already a type error in well-typed Simple, so the defect is
  a wrong-answer-on-an-already-odd-program, not something a correct program trips daily.
  That is a severity qualifier, not an exoneration: the whole point of the `-1` sentinel
  is to be the recognisable answer in exactly that situation, and this replaces it.
- **Which lanes actually select the Cranelift backend** for a hosted `native-build` (vs
  LLVM) was not enumerated. The LLVM `len` fast path referenced at `helpers.rs:64-65`
  was not audited for the same collision — it may or may not share the defect.
- **Whether the `28ff5e05494` in-guest bug is still live** (i.e. whether removing the arm
  would actually regress anything today) was not checked.
- **Which runtime actually wins for `rt_len` on any given hosted link** was not
  determined — only that both archives are present and that first-wins ordering decides
  it per symbol (`linker.rs:1624-1652`). Establishing the winner needs an `nm` on a real
  link artifact, which requires a build and was therefore out of scope.
- `git blame` on the arm points at `ae55a7467197` (2026-08-11, "fix(vcs): restore tree
  wiped by 6f86ff32a7d"), which is a tree-restore and hides authorship. The real
  introduction is `28ff5e05494` (2026-07-14), found via `git log -S"is_spldict"`.

## Related

- PR #257 — "fix(baremetal): decode the tagged bool in `rt_value_unbox_int`, and cover the
  riscv64 freestanding heap tags". **OPEN, not merged** as of 2026-09-06. Same root theme
  (freestanding vs hosted tag spaces conflated in seed codegen); its `InstrContext`
  target plumbing is the natural carrier for the fix above.
- `28ff5e05494` (2026-07-14) — "fix(seed/cranelift): handle simple-core SplDict (tag 6,
  len@16) in `inline_runtime_len_value`" — the commit that introduced the ungated arm.
