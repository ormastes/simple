# Array / List / Buffer Value ABI Contract

Status: **NORMATIVE (target) / partially RED on `origin/main`**. This document
specifies what MUST be true of the array-family value representation across all
three code trees and all three execution engines. Where current behavior
diverges from the rule, the divergence is named as a defect, not as an
alternative policy.

## Why this document exists

The ~131 open array/list/slice/buffer defects in `doc/08_tracking/bug/` are not
131 independent bugs. They are the same undocumented ABI being re-derived
ad-hoc at each call site. There is no single owner of the representation, so
every tree and every engine invented its own answer to the same four questions.
Cite this document by section when fixing one of them.

### The three trees (never two)

| # | tree | role |
|---|---|---|
| T1 | `src/compiler_rust/**` | Rust bootstrap **seed**. Disposable, but currently owns MIR lowering decisions. |
| T2 | `src/compiler/**`, `src/lib/**` | pure-Simple self-hosted compiler + stdlib. |
| T3 | `src/runtime/*.c` | the C runtime the self-hosted binary links, and what firmware externs call directly. |

A fix landed in one tree is **not** a fix. See
`.claude/memory/reference_three_implementations_not_two_seed_pure_simple_and_runtime_c.md`.

### The three engines

interpreter (tree-walking), Cranelift JIT, LLVM/Cranelift AOT native. `bin/simple test`
exercises the **interpreter only**, so no spec in the corpus can catch a
JIT-or-native-only ABI violation. Fences for this ABI belong in
`scripts/check/*.shs` (existing: `check-untyped-list-element-shift.shs`).

---

## §1 Tag/untag boxing scheme

### §1.1 Normative layout

An `ANY`-typed slot holds a **tag-boxed word**. For integers the encoding is a
pure arithmetic shift — no tag bits are OR'd in:

```
encode(v) = v << 3        // low 3 bits always 000; negative values shift arithmetically
decode(w) = w >> 3        // arithmetic right shift
```

Measured witness: `1→8`, `3→24`, `7→56`, `0→0`, `-1→-8`. Usable payload is
**61 bits**; `2^60-1` round-trips. `RT_NIL = 3` is a reserved sentinel, so `3`
must never be used as a probe value in an ABI test.

**MUST**: only integer-kind payloads (`i8..i64`, `u8..u64`, `bool`) are shifted.
Struct, class, enum and heap pointers are stored **unshifted**; floats are
heap-boxed with their own encode/decode arms. Applying `>>3` to an unshifted
pointer is type confusion and shreds the value (SIGSEGV or garbage).

**MUST**: a value wider than the 61-bit payload MUST be heap-boxed; silently
truncating is a violation. Measured consequence of the old unchecked encoder:
`2^60` came back negative, `i64::MAX` as `-1`, `2^62` as `0`
(`doc/08_tracking/bug/int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md`).

Conformance as of 2026-08-09:

- **T3 C runtime — CONFORMS.** `rt_value_int_wide` / `rt_value_as_int_wide`
  (`runtime_native.c`) keep the bit-identical `v << 3` immediate in range and
  heap-box out-of-range values as an `RT_VALUE_HEAP_INT` (`RtCoreWideInt`, same
  leaf layout as `RtCoreFloat`). Pinned by
  `src/runtime/test/rt_value_int_wide_selfcheck.c` (sabotage-verified).
- **T2 pure-Simple — CONFORMS in source.** `box_runtime_value` /
  `decode_runtime_value` route `I64`/`U64` through those two calls; kinds
  ≤ 32 bits keep the inline shift, since their payload cannot overflow.
- **T1 seed Cranelift JIT — VIOLATES.** Still truncates, and does so for plain
  scalars as well as container elements. The runtime entry points it needs
  already exist and are linked; see the bug file's "Defect A" section.

### §1.2 When a value is tagged

The tag/untag decision is made **at MIR construction time**, not per backend, so
it is shared by JIT and AOT:

- T1 seed: `mir/lower/lowering_expr_struct.rs::lower_index_expr` computes
  `element_expr_ty` and sets
  `needs_int_unbox = matches!(ty, I8|I16|I32|I64|U8|U16|U32|U64|BOOL)`. If false,
  **no `UnboxInt` is emitted** and the raw tagged word flows on.
  `rt_array_get` / `rt_index_get` **always** return a tagged word.
- T2 pure-Simple: `50.mir/_MirLoweringExpr/expr_dispatch.spl::box_runtime_value` /
  `decode_runtime_value`, driven by `note_container_elem_type`.
- T3 C: `runtime_native.c` reads `((int64_t*)array->data)[idx]` and applies
  `value >> 3` at `:2034`.

**MUST**: every consumer of an `ANY` slot decodes exactly once, at the point the
value acquires a concrete static type. Any arithmetic, comparison-against-a-
variable, or bit operation on an undecoded word is a violation of this section.
(The 2026-08-08 seed fix in `lowering_expr_ops.rs::lower_binary_expr` — unbox
the ANY side of a mixed binop — is the correct shape; the same rule MUST hold in
T2 and T3.)

**Current conformance**: interpreter CONFORMS (it inspects each `RuntimeValue`
tag dynamically). Seed Cranelift JIT VIOLATES. Pure-Simple AOT native CONFORMS
(measured). Pure-Simple JIT UNVERIFIED — treat as non-conforming until probed.

### §1.3 `list` vs `[T]` — the normative rule

> **NORMATIVE: `list` and `list<T>` MUST NOT be used as a parameter type
> anywhere in the codebase. Declare `[T]`.**

Rationale — this is a *typing* rule, not a workaround:

- `list` resolves (T1 `hir/lower/type_resolver.rs`) to
  `HirType::Array { element: ANY }`. The element type is **genuinely `ANY`**, so
  `needs_int_unbox = false` is *correct by the type system*. One callee body
  serves all call sites, so a blanket unbox would be unsound. There is no
  compiler fix that makes `list` safe without changing what `list` means.
- `list<T>` is **equally unsafe**: the container *spelling* decides, and the
  generic argument is discarded at HIR lowering. Do not assume the annotation
  helps.
- The defect is **declaration-site (callee-side)**. A caller passing a
  well-typed `[i64]` into a `data: list` parameter still corrupts. Cross-module
  vs same-module is irrelevant; standalone single-file probes reproduce.
- Locally-constructed lists inside a function body are fine — the type is known
  there. Only the parameter spelling loses it.

Affected read shapes (all VIOLATIONS when the container is `list`): `data[i] + x`,
`for x in data`, `data[i] > variable`, nested `rows[0][1]`, variable index,
propagation into further calls. Accidentally-safe shapes that MUST NOT be relied
on: `data.len()`, `data[i] = v` writes, compare-against-a-**literal**, both-sides-
tagged compares (the factor cancels), and `as u32` casts.

Scale: 1,356 `list`-spelled declarations across 180 files; ~750 sites carry the
live indexed-read shape; 49 sites are narrowed high-confidence arithmetic
victims (37 in `src/os/`, 12 in `src/lib/`). Confirmed corrupt production code
includes `rsa_pkcs1.spl` `_p_*`, `curve25519_bigint.spl`, `ed448.spl`,
`aes/padding.spl::pkcs7_unpad` (fails **open** — never strips), `bcrypt/salt.spl`,
`hotp.spl::_dynamic_truncate`, `bip39.spl::_set_bit`.

Related sibling defects that MUST be fixed to the same rule: `.at(i)` returns a
raw word; `.get(i)` type-errors in the interpreter but returns a tagged word
under JIT; an `ANY` receiver read into `val b: u32 = dst[i]` returns `v<<3` while
bare `val a = dst[i]` lowers a subsequent `a >> 24` to **floating point**.

---

## §2 Element width and packed-buffer representation

### §2.1 Current representation

```c
typedef struct RtCoreArray {          // src/runtime/runtime_native.c:806
  uint8_t  kind; uint8_t flags; uint16_t reserved;
  uint32_t transient_scope_id;
  int64_t  len; int64_t cap; void* data;
} RtCoreArray;
```

`elem_size` is **binary — 1 or 8, nothing else**:
`(flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t)`,
repeated at `runtime_native.c:5218` (alloc), `:5997` (copy), `:6169` (realloc).
The T2 mirror hardcodes `idx * 8` in all four accessors
(`.../core_array_ops.spl:382`). `RT_CORE_ARRAY_FLAG_U64_PACKED` controls
**tagging only, never width**.

**Consequence**: `[u32]` is *not a packed buffer*. It is an array of 8-byte
slots holding `v<<3`. `rt_typed_words_u32_*` is an 8-byte-stride read masked to
32 bits. The only genuinely packed basis today is a BYTES array plus
`rt_typed_bytes_u32_le_at/set`.

### §2.2 What this breaks

- **SIMD**: `_mm_loadu_si128` / `vld1q_u8` require a contiguous `uint8_t*`.
  Bulk copy over `[u8]` is unreachable; the shipped workaround
  (`rt_array_extend_i64`) has no SIMD path. `zstd.spl:1119` carries a dead NEON
  chunk width as a result.
- **Pixel buffers**: every framebuffer path pays a representation conversion —
  `backend_software.spl:615` does one FFI round trip per row;
  `runtime_rocm.c:507,539` mallocs a real `uint32_t[]` and gathers element-wise.
- **Crypto/byte externs**: FFI marshalling must special-case tagged vs raw
  elements (`expect_byte_array` once accepted only `Value::Int` and failed every
  AES KAT).
- Cranelift `[u8]` array literals emit garbage data pointers under freestanding
  `x86_64-unknown-none` — OPEN.

### §2.3 Normative target (SPEC ONLY — do not implement here)

A conforming runtime MUST support **width as a first-class array property**, not
a boolean:

1. Replace the BYTES boolean with an explicit `uint8_t elem_width` field taking
   `1 | 2 | 4 | 8`, with `elem_size` derived from it in exactly one place per
   tree. No call site may re-derive a stride.
2. Packed widths (`1|2|4`) are **untagged by construction** — the payload does
   not fit a tag and MUST NOT be shifted. `<<3` applies only to `elem_width == 8`
   `ANY` slots. §1 and §2 meet exactly here.
3. `data` MUST be `elem_width`-aligned and contiguous with no per-element header,
   so `(uint8_t*)data` is directly loadable by SIMD and passable to an extern
   without a gather.
4. The width MUST be carried in the static type (`[u32]` implies width 4), so
   the compiler, not the runtime, decides it; a runtime that infers width from a
   flag at read time is non-conforming.
5. Bounds and OOB behavior are unchanged by width; an OOB read MUST NOT leak the
   raw `RT_NIL` sentinel (see `jit_array_oob_read_leaks_raw_rt_nil_sentinel`).

Until (1)–(5) land, any code claiming `[u32]` is a packed buffer violates this
section.

---

## §3 Value vs reference and mutation semantics

### §3.1 The rule

> **NORMATIVE: arrays are value types with copy-on-write. Passing an array
> copies it observably; mutation inside a callee is invisible to the caller
> unless the callee's result is reassigned (`arr = modify(arr)`). Class instances
> remain reference types.**

CoW is an *implementation* of that rule, not an exception to it: `Arc` binding
plus clone-on-write gives O(1) parameter passing while preserving observable
copy semantics. Both halves are required — an implementation that is O(1) but
aliases is non-conforming, and one that deep-copies on every call is conforming
but violates the performance expectation and MUST be treated as a defect too.

### §3.2 `mut` parameters

Copy-out write-back is the current seed mechanism
(`interpreter_call/core/function_exec.rs::write_back_mutable_arguments`). It is
non-conforming in two specific ways that MUST be fixed:

- It writes back **all** identifier-bound container arguments regardless of
  `Parameter.mutability`. Normative: write back **only** parameters declared
  `mut`.
- Write-back is keyed by the caller's binding **name**, so aliasing breaks it and
  non-identifier arguments (spread, variadic, field paths) silently skip it.
  Normative: passing the same array as both a `mut` and a non-`mut` argument in
  one call MUST be a compile error, not a last-write-wins clobber.

T2 implements **neither** copy: `10.frontend/core/interpreter/eval_calls.spl`
(~332) copies only value-type structs, and `95.interp/mir_interpreter.spl` uses
flat addresses. Arrays are fully aliased in both. That is the largest single
conformance gap in this section.

### §3.3 Conformance matrix

| boundary | interpreter (T1) | JIT | AOT native |
|---|---|---|---|
| same-fn `arr[i] = v` | CONFORMS | CONFORMS | CONFORMS |
| same-fn `push/pop/insert/remove` | CONFORMS (was O(N²) clone — FIXED 2026-07-07) | CONFORMS | — |
| read-only array param | CONFORMS (Arc, O(1)) | CONFORMS | — |
| `mut` param, non-aliased | CONFORMS | CONFORMS | — |
| same array as `mut` + non-`mut` | **VIOLATES** — mutation silently lost (OPEN 2026-08-06) | CONFORMS | — |
| cross-module + BDD `it` closure | FIXED 2026-07-15 | CONFORMS | — |
| module-level `var` array via receiver-less free fn | **VIOLATES** — stale snapshot (OPEN 2026-07-29) | — | — |
| module-level array `.get(i)` | **VIOLATES** — `unknown extern rt_args_count` (OPEN) | — | — |
| first-class fn value / stored handler field | **VIOLATES** — writeback erratically dropped (OPEN 2026-08-09) | — | — |
| struct field array via nested `me` | **VIOLATES** — `CowEnv::get_mut` clones whole array per write | — | — |
| `list.first()` | **VIOLATES** — returns raw nilable, not `Option<T>` (OPEN) | — | — |

Blank cells are **unverified, not passing**. LLVM AOT is essentially uncovered
for this section — that is itself a conformance gap.

---

## §4 UTF-8 slice boundary policy

Three live policies exist for one operation. Probe `s = "aé€𝄞z"`, `s[0:2]`
splits `é`:

| policy | result | where |
|---|---|---|
| P1 raw bytes, no validation | `61 c3`, len 2, **invalid UTF-8** | `runtime_native.c:3110` (`rt_slice`); `core_string.spl:614`; seed bracket slice `interpreter/expr/collections.rs:441`; `spl_str_slice` in **both** `runtime.c:311` and `runtime_legacy_core.c:182` (duplicated, divergent on negative indices, resolved by link order under `-z muldefs`) |
| P2 lossy `U+FFFD` | `61 efbfbd`, len 4 | seed `interpreter_method/string.rs:327` (`String::from_utf8_lossy`) |
| P3 clamp to a boundary | not implemented | proposed and rejected |

### §4.1 The rule

> **NORMATIVE: slicing a text value at a non-character boundary is an ERROR.**
> The operation MUST fail loudly (trap / `Err`), never return a value.

Why the other two are wrong:

- **P1 is wrong** because it manufactures a value that is not text. Every
  downstream invariant ("a text is valid UTF-8") is now false, and the corruption
  surfaces arbitrarily far away — the failure is unattributable to the slice.
  A `native-build` binary now ships this truncation in standalone output.
- **P2 is wrong** because it silently *changes the data*. `U+FFFD` is a lossy
  edit presented as a successful slice; round-trips break with no error, and it
  makes P1's byte-count and P2's byte-count disagree for the same expression, so
  the same program means two things on two engines.
- **P3 is wrong** because clamping silently returns a **different range** than
  the one requested. A caller asking for `[0:2]` and receiving `[0:1]` has no
  signal that its index arithmetic is broken.

Only the error policy preserves both "text is valid UTF-8" and "the result is
the range you asked for". Validation routes through the existing
`scalar_utf8_validate` / `rt_text_validate_utf8`
(`runtime_simd_utf8.c:185`, `runtime.h:1089`) — no new machinery is required.

### §4.2 Scoping and migration

- **Byte arrays are exempt.** `FLAG_BYTES` slicing is a byte operation with no
  UTF-8 invariant; it MUST keep raw-byte behavior.
- The flip is **DEFERRED**, not disputed: a census found 1,427 violating sites
  across 39 spec files, of which 87.9% are the single-byte scanner idiom
  `s[i:i+1]`. The migration target is `byte_at` (landed,
  `runtime_native.c:2372`); ~891 static sites remain.
- The duplicate `spl_str_slice` definitions MUST be collapsed to one before the
  flip; otherwise the policy is decided by link order.

---

## §5 How to verify a fix conforms

Run all of these. A fix that passes only some of them is not landed.

1. **Three trees.** Did you change T1 (`src/compiler_rust`), T2
   (`src/compiler`/`src/lib`), and T3 (`src/runtime/*.c`)? If you changed one,
   state explicitly why the other two were already correct — do not assume it.
   Grep for a duplicated definition (`spl_str_slice` is the cautionary case);
   `-z muldefs` makes a duplicate symbol silent, not fatal.
2. **Three engines.** Re-run the probe under the interpreter
   (`SIMPLE_EXECUTION_MODE=interpret`), under JIT (any other value — unknown
   values **fail open to JIT**; `SIMPLE_NO_JIT=1` is a no-op on the seed), and
   under `native-build`. A green `bin/simple test` proves the interpreter only.
3. **Sabotage the oracle.** Before believing a pass, break the implementation on
   purpose and confirm the probe goes red. Symbol-sweep and absence-based checks
   in this repo fail open.
4. **§1 probe.** Read an element and do *arithmetic on a variable* with it —
   not a literal, and not both-sides-tagged; those shapes cancel the `<<3` and
   pass vacuously. Avoid the value `3` (`RT_NIL`).
5. **§1.3 grep.** `grep -rE ':\s*list(<[^>]*>)?\s*[,)]' src/ --include='*.spl'`
   must not grow. Note `grep` here is a wrapped `ugrep` honouring `.gitignore` —
   use `/usr/bin/grep` for any load-bearing count.
6. **§2 stride.** Confirm no new call site re-derives an element stride. There
   must be exactly one `elem_size` derivation per tree.
7. **§3 aliasing.** Probe caller-observable state after the callee returns, at
   each boundary in the §3.3 matrix that your change touches — including the
   aliased `mut`/non-`mut` case and a first-class-fn call.
8. **§4 boundary.** Slice a multi-byte character at a non-boundary index and
   confirm the same outcome on all three engines. Byte arrays must be unaffected.
9. **Fence, not spec.** Because the spec corpus cannot see JIT/native, add or
   extend a `scripts/check/*.shs` guard with a fixture under `test/fixtures/`.
   Verify the guard is fail-**closed**: run it against a deliberately broken
   fixture and confirm a non-zero exit.

## References

- `doc/08_tracking/bug/untyped_list_element_read_seed_rootcause_2026-07-30.md`
- `doc/08_tracking/bug/untyped_list_param_census_2026-07-29.md`
- `doc/08_tracking/bug/native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`
- `doc/08_tracking/bug/any_receiver_element_read_shift_and_tag_2026-08-06.md`
- `doc/08_tracking/bug/jit_list_param_miscompile_boundary_map_2026-08-08.md`
- `doc/08_tracking/bug/aliased_array_mut_param_mutation_lost_interpreter_2026-08-06.md`
- `doc/08_tracking/bug/bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md`
- `doc/04_architecture/ui/rendering/exact_8bit_pixel_formula.md` §6
