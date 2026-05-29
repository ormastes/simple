# Wave-1 C Runtime Modules — Conversion Research

**Date:** 2026-05-18  
**Scope:** 9 "easy" C runtime files in `src/runtime/` that are candidates for pure-Simple replacement.  
**Goal:** Document every exported function, locate existing Simple equivalents, identify dependencies, assess difficulty, and note how each is wired into the compiler.

---

## 1. `runtime_ctype.c` (10 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `__is_alnum` | `(i32) -> i32` | Delegates to `isalnum(3)` |
| `__is_alpha` | `(i32) -> i32` | Delegates to `isalpha(3)` |
| `__is_digit` | `(i32) -> i32` | Delegates to `isdigit(3)` |
| `__is_xdigit` | `(i32) -> i32` | Delegates to `isxdigit(3)` |
| `__is_space` | `(i32) -> i32` | Delegates to `isspace(3)` |
| `__is_lower` | `(i32) -> i32` | Delegates to `islower(3)` |
| `__is_upper` | `(i32) -> i32` | Delegates to `isupper(3)` |

### Dependencies
- `<ctype.h>` locale-aware C standard library only. No other runtime files.

### Existing Simple Equivalent
None found in `src/lib/`. The `src/lib/common/` tree has no `ctype.spl`.

### Compiler Wiring
No hits in `src/compiler_rust/` or `src/compiler/` for `__is_alnum` etc. — likely called by generated code or string stdlib, not directly by the codegen pass. Needs deeper grep to confirm call sites.

### Conversion Difficulty: **Trivial**
Each function is a 1-liner delegating to a C standard function. In Simple these are straightforward bitrange checks on ASCII scalar values — no heap allocation, no runtime value boxing. The only subtlety is locale independence: the C functions are locale-sensitive; a pure-Simple version should use Unicode code-point logic or explicit ASCII table. For ASCII-only use (which is the current semantic) this is trivially expressible with `ch >= 'a' && ch <= 'z'` style guards.

### Performance Notes
Not performance-critical. Called in character-classification inner loops for lexing/parsing; inlining in Simple will be at least as fast as the C thunk.

---

## 2. `runtime_hash.c` (13 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_fnv_hash` | `(*u8, u64) -> u64` | FNV-1a 64-bit hash over a byte slice |

### Dependencies
- `<stdint.h>`, `<stddef.h>`. No other runtime files.

### Existing Simple Equivalent
**Yes — partial.** `src/lib/nogc_sync_mut/src/hash.spl` implements FNV-1a for the `Hash` trait on `text` and integers. The constants (`FNV_OFFSET`, `FNV_PRIME`) and algorithm match exactly. However the Simple version operates on the `bytes()` iterator of a `text` value, not on a raw `(*u8, len)` slice pair.

### Compiler Wiring
No direct hits for `rt_fnv_hash` in compiler Rust or Simple sources — it appears to be an internal utility, possibly called by string hashing paths in the interpreter, not directly emitted by codegen.

### Conversion Difficulty: **Trivial**
Pure byte loop, two constants. The existing `hash.spl` FNV-1a body can be extracted as a standalone `fn fnv_hash(data: [u8]) -> u64` with minimal adaptation. The raw-pointer ABI (`*u8 + len`) maps to a Simple `[u8]` slice.

### Performance Notes
This IS a hot path for hash table operations. The Simple compiler should inline or optimize this. Profile after conversion.

---

## 3. `runtime_config.c` (21 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_set_macro_trace` | `(bool) -> void` | Atomically set global macro-trace flag |
| `rt_is_macro_trace_enabled` | `() -> bool` | Read macro-trace flag with seq_cst ordering |
| `rt_set_debug_mode` | `(bool) -> void` | Atomically set global debug-mode flag |
| `rt_is_debug_mode_enabled` | `() -> bool` | Read debug-mode flag with seq_cst ordering |

### Dependencies
- `<stdatomic.h>`, `<stdbool.h>`. Uses `atomic_bool` globals with `memory_order_seq_cst`. No other runtime files.

### Existing Simple Equivalent
None. `src/lib/nogc_sync_mut/src/dl/config.spl` and `src/lib/nogc_sync_mut/src/exp/config.spl` are application-level, not compiler runtime.

### Compiler Wiring
`src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` line 98: `name.starts_with("rt_set_macro_trace")` — confirming the Rust codegen references these symbols by name. They are registered in the runtime FFI function table.

### Conversion Difficulty: **Easy** (with caveat)
The logic is two pairs of get/set. The caveat: `atomic_bool` with `seq_cst` ordering. Simple currently has no built-in atomic primitives exposed at the language level for compiler-internal runtime use. Options:
1. Keep as a thin C shim and do not convert yet (deferred until Simple gets `@atomic` or similar).
2. Convert to non-atomic (only safe if macro_trace is always set at startup before threads start).
3. Use an `extern` to an OS-level atomic in Simple (possible but complex).

**Recommendation:** Defer to Wave-2 pending atomic primitive support.

### Performance Notes
Called rarely (at startup / debug flag toggle). Not performance-critical.

---

## 4. `runtime_math.c` (50 LOC)

### Exported Functions (29 total)
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_math_pow` | `(f64, f64) -> f64` | `pow` |
| `rt_math_log` | `(f64) -> f64` | natural log |
| `rt_math_log10` | `(f64) -> f64` | log base 10 |
| `rt_math_log2` | `(f64) -> f64` | log base 2 |
| `rt_math_exp` | `(f64) -> f64` | `e^x` |
| `rt_math_sqrt` | `(f64) -> f64` | square root |
| `rt_math_cbrt` | `(f64) -> f64` | cube root |
| `rt_math_sin` | `(f64) -> f64` | sine |
| `rt_math_cos` | `(f64) -> f64` | cosine |
| `rt_math_tan` | `(f64) -> f64` | tangent |
| `rt_math_asin` | `(f64) -> f64` | arc sine |
| `rt_math_acos` | `(f64) -> f64` | arc cosine |
| `rt_math_atan` | `(f64) -> f64` | arc tangent |
| `rt_math_atan2` | `(f64, f64) -> f64` | atan2 |
| `rt_math_sinh` | `(f64) -> f64` | hyperbolic sin |
| `rt_math_cosh` | `(f64) -> f64` | hyperbolic cos |
| `rt_math_tanh` | `(f64) -> f64` | hyperbolic tan |
| `rt_math_floor` | `(f64) -> f64` | floor |
| `rt_math_ceil` | `(f64) -> f64` | ceil |
| `rt_math_round` | `(f64) -> f64` | round half-away |
| `rt_math_trunc` | `(f64) -> f64` | truncate toward zero |
| `rt_math_abs` | `(f64) -> f64` | absolute value |
| `rt_math_hypot` | `(f64, f64) -> f64` | Euclidean distance |
| `rt_math_gcd` | `(i64, i64) -> i64` | GCD via Euclidean algo |
| `rt_math_min` | `(f64, f64) -> f64` | float min |
| `rt_math_max` | `(f64, f64) -> f64` | float max |
| `rt_math_clamp` | `(f64, f64, f64) -> f64` | clamp in range |
| `rt_math_fma` | `(f64, f64, f64) -> f64` | fused multiply-add |

### Dependencies
- `<math.h>`, `<stdint.h>`, `<stdlib.h>`. Thin wrappers over libm. No other runtime files.

### Existing Simple Equivalent
Partial. `src/lib/common/math.smf` exists but is a module manifest. `src/compiler/90.tools/ffi_gen/specs/math.spl` declares these as FFI specs pointing back to the C functions — so the Simple compiler already knows the mapping. There is **no pure-Simple implementation** of transcendentals (`sin`, `cos`, etc.) in the lib tree.

### Compiler Wiring
Heavily wired. `src/compiler/90.tools/ffi_gen/specs/math.spl` enumerates every `rt_math_*` function with `runtime_fn` annotations. Both Cranelift and LLVM codegen backends reference these names. The `rt_math_gcd` is also wired for the `gcd()` builtin.

### Conversion Difficulty: **Mixed**
- `rt_math_gcd`, `rt_math_clamp`, `rt_math_min`, `rt_math_max`: **Trivial** — pure integer/float arithmetic expressible directly in Simple.
- `rt_math_floor`, `rt_math_ceil`, `rt_math_round`, `rt_math_trunc`, `rt_math_abs`: **Easy** — these map to intrinsic LLVM/Cranelift ops; Simple can emit them as built-ins or `@llvm.floor` etc.
- Transcendentals (`sin`, `cos`, `tan`, `log`, `exp`, `sqrt`, `pow`, ...): **Medium** — these require libm on the target. Conversion means calling the platform libm via Simple `extern` rather than through the C shim. This is structurally the same call depth but eliminates one extra indirection. The FFI spec generator in `90.tools/ffi_gen` is the correct place to do this — replace `runtime_fn` with a direct `extern` declaration in Simple.

### Performance Notes
`rt_math_sqrt`, `rt_math_sin`, `rt_math_cos`, and the trig family are called in hot rendering/physics paths in game2d and gpu libraries. Keep libm delegation unchanged; the value is eliminating the C shim file from the build, not rewriting the math.

---

## 5. `runtime_error.c` (25 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_function_not_found` | `(*u8, u64) -> RuntimeValue` | Print "Function not found" to stderr, return RT_ERROR |
| `rt_method_not_found` | `(*u8, u64, *u8, u64) -> RuntimeValue` | Print "Method not found" to stderr, return RT_ERROR |

### Dependencies
- `runtime_value.h` (for `RT_ERROR` constant and `RuntimeValue` typedef)
- `<stdio.h>` for `fprintf`
- `<stdint.h>`

### Existing Simple Equivalent
None. These are compiler-internal error reporters, not user-facing library functions.

### Compiler Wiring
Heavily wired into Cranelift codegen:
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` calls `rt_function_not_found` at lines 545, 571, 584
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` line 193: listed as a required root symbol
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` registers it in the FFI function table

### Conversion Difficulty: **Easy** (with dependency note)
Logic is `fprintf(stderr, ...) + return RT_ERROR`. In Simple this would be:
```
extern fn rt_function_not_found(name_ptr: *u8, name_len: u64) -> RuntimeValue:
    stderr.write("Runtime error: Function '{name}' not found\n")
    RT_ERROR
```
The blocker: `RuntimeValue` is a C `uint64_t` tagged union. Simple does not yet have a direct way to construct and return the bit-pattern `RT_ERROR` (which is `((3 << 3) | 3)` = `0x1B`). Requires either a `const` `@bits` literal or a companion SFFI primitive. This is solvable but needs care.

### Performance Notes
Error path — not performance-critical.

---

## 6. `runtime_contracts.c` (63 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `simple_contract_check` | `(i64 cond, i64 kind, *u8 fn_name, i64 fn_len) -> void` | If cond==0, print violation message and `abort()` |
| `simple_contract_check_msg` | `(i64 cond, i64 kind, *u8 fn_name, i64 fn_len, *u8 msg, i64 msg_len) -> void` | Same but with user message |

Both use an internal `contract_kind_name(kind)` that maps 0–5 to `"Precondition"`, `"Postcondition"`, `"Error postcondition"`, `"Entry invariant"`, `"Exit invariant"`, `"Assertion"`.

### Dependencies
- `<stdint.h>`, `<stdio.h>`, `<stdlib.h>` (for `abort()`), `<string.h>`. No other runtime files.

### Existing Simple Equivalent
None for the runtime ABI. The `@require`/`@ensure` language annotations in Simple source generate calls to these C functions.

### Compiler Wiring
Both Cranelift and LLVM backends reference these:
- `src/compiler_rust/compiler/src/codegen/instr/contracts.rs` line 38–39: emits call to `simple_contract_check`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` lines 2096–2097: special handling for `simple_contract_check` and `simple_contract_check_msg`
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs` lines 109–110: same for LLVM backend

### Conversion Difficulty: **Easy**
The function bodies are `fprintf` + `abort()`. In Simple:
- `abort()` maps to a `@panic` or `rt_abort()` extern.
- `fprintf(stderr, ...)` maps to Simple's stderr write.
- The `contract_kind_name` switch is a simple `match kind { 0 => "Precondition", ... }`.

The only subtlety is that `abort()` must be a genuine process-terminating extern, not a Simple exception. Simple has `@panic` which maps correctly.

### Performance Notes
Compiled-out in release builds if contracts are disabled. Not performance-critical in normal operation.

---

## 7. `runtime_value.c` (41 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_value_int` | `(i64) -> RuntimeValue` | Box i64 into tagged RuntimeValue |
| `rt_value_float` | `(f64) -> RuntimeValue` | Box f64 into tagged RuntimeValue |
| `rt_value_bool` | `(bool) -> RuntimeValue` | Box bool into tagged RuntimeValue |
| `rt_value_nil` | `() -> RuntimeValue` | Return RT_NIL |
| `rt_value_as_int` | `(RuntimeValue) -> i64` | Unbox to i64 |
| `rt_value_as_float` | `(RuntimeValue) -> f64` | Unbox to f64 |
| `rt_value_as_bool` | `(RuntimeValue) -> bool` | Unbox to bool |
| `rt_value_truthy` | `(RuntimeValue) -> bool` | Truthiness test (nil/false = false, else true) |
| `rt_value_is_nil` | `(RuntimeValue) -> bool` | Tag check: nil |
| `rt_value_is_int` | `(RuntimeValue) -> bool` | Tag check: int |
| `rt_value_is_float` | `(RuntimeValue) -> bool` | Tag check: float |
| `rt_value_is_bool` | `(RuntimeValue) -> bool` | Tag check: bool |
| `rt_value_is_heap` | `(RuntimeValue) -> bool` | Tag check: heap pointer |
| `rt_value_type_tag` | `(RuntimeValue) -> u8` | Extract 3-bit tag |
| `rt_is_error` | `(RuntimeValue) -> bool` | Check if RT_ERROR |
| `rt_ptr_to_value` | `(*u8) -> RuntimeValue` | Cast heap pointer to RuntimeValue with TAG_HEAP |
| `rt_value_to_ptr` | `(RuntimeValue) -> *u8` | Extract heap pointer from RuntimeValue |

### Dependencies
- `runtime_value.h` — defines the `RuntimeValue = uint64_t` typedef and all `rv_*` inline helpers via C macros. Every function in this file is a one-liner delegating to the header macros.

### Existing Simple Equivalent
**Partial.** `src/compiler/70.backend/ffi_minimal.spl` already declares `extern fn rt_value_int`, `extern fn rt_value_float`, and `extern fn rt_value_eq` — showing the Simple compiler backend knows these symbols. These are not re-implemented in Simple; they are extern-declared to call the C versions.

### Compiler Wiring
- `src/compiler/70.backend/ffi_minimal.spl` lines 46–47, 87: `extern fn rt_value_int`, `extern fn rt_value_float`, `extern fn rt_value_eq`
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` line 371: `RuntimeFuncSpec::new("rt_value_eq", ...)`

### Conversion Difficulty: **Medium**
All logic lives in the `runtime_value.h` inline macros (bit manipulation on a `u64`). In Simple these would be `@inline` functions operating on `u64` with bitwise operators. The tag scheme is:
- bits 0–2 = tag (`0`=int, `1`=heap, `2`=float, `3`=special)
- int: value << 3
- float: bit-cast f64, shift out 3 LSBs (lossy for denormals — known limitation)
- heap: pointer | TAG_HEAP

The medium difficulty comes from the need for `@bits` casting (`f64 <-> u64`) and ensuring the Simple type system allows raw `u64` pointer packing. Once SFFI/custom-primitive support is confirmed stable (it landed in the previous wave), this becomes straightforward.

### Performance Notes
**HOT PATH.** `rt_value_truthy`, `rt_value_is_*`, and boxing/unboxing are called on every interpreter value operation. Must be inlined. Converting to Simple only makes sense if the compiler can guarantee inlining comparable to C `static inline`.

---

## 8. `runtime_equality.c` (126 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_value_eq` | `(RuntimeValue, RuntimeValue) -> u8` | Deep equality: int, float, bool, string (memcmp), enum (recursive) |
| `rt_value_compare` | `(RuntimeValue, RuntimeValue) -> i64` | Three-way comparison (-1/0/1): int, float, string (lexicographic), mixed int/float |
| `rt_native_eq` | `(i64, i64) -> i64` | Equality for heap-tagged values passed as raw i64; delegates to `rt_value_eq` |
| `rt_native_neq` | `(i64, i64) -> i64` | Not-equal; delegates to `rt_native_eq` |

### Dependencies
- `runtime_value.h` (for all `rv_*` macros, heap type constants `HEAP_TYPE_STRING`, `HEAP_TYPE_ENUM`, `RuntimeString`, `RuntimeEnum`)
- `<stdbool.h>`, `<math.h>` (for `fpclassify`, `FP_SUBNORMAL`)
- `<string.h>` (for `memcmp`)

### Existing Simple Equivalent
None for the runtime ABI. The Simple lib `hash.spl` has `impl Hash for text` but no structural equality.

### Compiler Wiring
- `src/compiler/70.backend/ffi_minimal.spl` line 87: `extern fn rt_value_eq(...) -> bool`
- `src/compiler/70.backend/backend/llvm_lib_translate.spl` line 246: declares `rt_value_eq` LLVM function type
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` lines 371–372: registers `rt_value_eq` and `rt_value_compare`
- `src/compiler_rust/compiler/src/codegen/instr/core.rs` line 376: comment notes `rt_value_eq` for tagged heap string comparison

### Conversion Difficulty: **Medium**
The core logic is clear: check tags, dispatch to type-specific comparison. The complexity is:
1. String equality uses `memcmp` on the inline bytes after `RuntimeString` header — requires raw pointer arithmetic in Simple.
2. `fpclassify(FP_SUBNORMAL)` guard in `rt_value_compare` — needs a Simple `@classify_float` or equivalent.
3. Recursive `rt_value_eq` for enum payloads — self-recursion is fine in Simple.
4. `MIN_HEAP_ADDR` guard (pointer sanity check) — needs `as u64` cast.

All solvable with SFFI and bitwise ops, but more boilerplate than the trivial files.

### Performance Notes
**HOT PATH.** Every `==` on non-primitive values goes through `rt_value_eq`. Must remain inlinable or intrinsic. Conversion feasibility depends on whether Simple can compile this to equivalent assembly.

---

## 9. `runtime_base64.c` (80 LOC)

### Exported Functions
| Function | Signature | Purpose |
|----------|-----------|---------|
| `__c_rt_base64_encode` | `(*u8 in, u64 in_len, *u8 out, u64 out_cap) -> i64` | Encode bytes to base64; returns written bytes or -1 on error |
| `__c_rt_base64_decode` | `(*u8 in, u64 in_len, *u8 out, u64 out_cap) -> i64` | Decode base64 to bytes; skips whitespace and `=` padding; returns written bytes or -1 |

### Dependencies
- `<stdint.h>`, `<stddef.h>`. Static lookup tables only. No other runtime files.

### Existing Simple Equivalent
**Yes — significant overlap.** `src/lib/common/base64/` directory exists with:
- `encode.smf`, `decode.smf`, `mod.smf`, `types.smf`, `utilities.smf`, `validation.smf`, `variants.smf`
- `src/lib/common/base_encoding/base64.smf` — another base64 module

These are higher-level Simple library modules (operating on `text`/`[u8]` types), not a direct ABI replacement for the raw `(*u8, len)` C function. The C function uses caller-provided output buffer (no allocation); the Simple version likely allocates.

### Compiler Wiring
No hits for `__c_rt_base64_encode`/`__c_rt_base64_decode` in `src/compiler_rust/` or `src/compiler/`. This suggests these functions are called from Simple lib code via `extern fn`, not directly from the codegen. Likely wired through `src/lib/common/base64/` internals.

### Conversion Difficulty: **Easy**
The algorithm is a self-contained byte-loop with a 64-entry encode table and 128-entry decode table. No heap allocation, no recursion, pure arithmetic. The existing `src/lib/common/base64/` library already has the higher-level encoding logic. The C functions can be replaced by:
1. Wrapping the existing Simple base64 lib to provide the raw-slice ABI, or
2. Rewriting the 80-LOC algorithm inline in Simple (trivial loop + table lookup).

The decode has one nuance: it skips whitespace and handles partial chunks (< 4 bytes). This is already handled in the C code and can be ported directly.

### Performance Notes
Not a hot path in the compiler itself. The existing Simple lib already exists — this is the easiest candidate for full conversion.

---

## Summary Table

| File | LOC | Exported Fns | Existing Simple | Difficulty | Hot Path | Blocker |
|------|-----|-------------|-----------------|------------|----------|---------|
| `runtime_ctype.c` | 10 | 7 | No | Trivial | No | Locale semantics (ASCII ok) |
| `runtime_hash.c` | 13 | 1 | Partial (hash.spl FNV-1a) | Trivial | Yes (hash tables) | None |
| `runtime_base64.c` | 80 | 2 | Yes (common/base64/) | Easy | No | None |
| `runtime_math.c` | 50 | 28 | No pure-Simple | Mixed | Yes (trig paths) | Transcendentals need libm extern |
| `runtime_error.c` | 25 | 2 | No | Easy | No | RT_ERROR bit-pattern construction |
| `runtime_contracts.c` | 63 | 2 | No | Easy | No | abort() extern |
| `runtime_config.c` | 21 | 4 | No | Easy (deferred) | No | atomic_bool — no Simple atomic |
| `runtime_value.c` | 41 | 17 | Partial (extern decls) | Medium | **Critical** | f64 bit-cast, inline guarantee |
| `runtime_equality.c` | 126 | 4 | No | Medium | **Critical** | memcmp, fpclassify, pointer arith |

## Recommended Conversion Order

1. **First wave (do now):** `runtime_ctype.c`, `runtime_hash.c`, `runtime_base64.c`  
   — Zero blockers, no hot-path risk, existing Simple lib overlap.

2. **Second wave:** `runtime_error.c`, `runtime_contracts.c`, subset of `runtime_math.c` (`gcd`, `clamp`, `min`, `max`, floor/ceil/round/trunc/abs)  
   — Minor blockers (RT_ERROR bit literal, abort extern) resolvable with one SFFI declaration.

3. **Third wave (needs care):** `runtime_math.c` transcendentals  
   — Replace C shim with `extern fn rt_math_sin(x: f64) -> f64` declared in Simple, delegating to platform libm. Structurally equivalent; the `90.tools/ffi_gen/specs/math.spl` spec file is the right place.

4. **Deferred:** `runtime_config.c` (until Simple gets atomic primitives), `runtime_value.c`, `runtime_equality.c` (until inlining guarantees are verified for hot paths).

## Key Findings

- **`runtime_value.h`** is the load-bearing dependency for `runtime_value.c`, `runtime_equality.c`, and `runtime_error.c`. Converting those three files requires either keeping the header as a C include or re-expressing the tag layout as Simple constants.
- **No Rust codegen** (`src/compiler_rust/`) calls `__c_rt_base64_*` or `__is_alnum` etc. directly — those go through Simple lib `extern fn` declarations.
- **Both Cranelift and LLVM backends** hardcode `simple_contract_check`, `rt_value_eq`, `rt_value_compare`, `rt_function_not_found` as named symbol references in `runtime_ffi.rs` and `calls.rs`. Converting these requires keeping the same exported symbol names in the Simple replacements.
- **`src/lib/nogc_sync_mut/src/hash.spl`** already contains a working FNV-1a implementation — `runtime_hash.c` is redundant and should be deleted after wiring `hash.spl` to the raw-slice ABI.
- **`src/lib/common/base64/`** already provides base64 in Simple — `runtime_base64.c` can be replaced by an ABI bridge to the existing library.
