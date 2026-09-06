# SFFI boundary: per-call allocations and an unfreed runtime string (2026-08-21)

Audit of the SFFI/extern boundary for per-call allocation, leaks, zero-slack
growth, and cross-boundary collection copies. The self-hosted compiler crosses
this boundary constantly (`rt_string_*`, `rt_array_*`, dict ops, file/env/path,
sha256, lexer char access), so a per-call allocation here is multiplied by the
whole compile.

Scope was limited to the SFFI/extern boundary: `interpreter_extern/**`,
`interpreter_sffi*.rs`, the `sffi_return_contract` path in
`interpreter_call/core/function_exec.rs`, `runtime/src/value/sffi/**`, and the
`src/runtime/*.c` marshalling helpers. No SFFI architecture or contract was
changed — no edit touches the extern declaration model, value marshalling
semantics, the return-contract validator's rules, or the `rt_*` ABI. Every fix
below is behaviour-preserving, including error precedence.

## Defects found and fixed

| # | Site | Mechanism | Evidence | Fix | Pre -> post |
|---|------|-----------|----------|-----|-------------|
| 1 | `compiler/src/interpreter_extern/sffi_string.rs` `rt_string_eq_fn` | **LEAK.** Both arguments went through `resolve_runtime_string`, which for any interpreter `text` of 2+ bytes calls `rt_string_new` -> `alloc_runtime_string` (a real heap allocation; only len 0 and len 1 hit the short-string cache). Nothing on this read-only comparison path ever called `rt_string_free`, so **every text/text comparison leaked two runtime strings permanently.** | `string_eq_does_not_leak_a_runtime_string_per_call` (sffi_string.rs) measures BOTH mechanisms in one process via `/proc/self/statm`: it replays the pre-fix `resolve_runtime_string` + `rt_string_eq` shape, then the current path, and asserts the current path's RSS growth is under 1/8 of the leaky one's. It also asserts the leaky shape *does* leak, so the test cannot pass vacuously. | Compare bytes directly. `borrowed_string_bytes` borrows a `Value::Str`; `handle_string_bytes` reads a runtime-string handle's registry buffer in place. Zero allocations. | **158 MB -> 0 MB** RSS growth over 20,000 comparisons of 4 KiB texts (measured 2026-08-21, printed by the test itself). 158 MB / 20,000 = ~8.3 KB per call = exactly the two 4 KiB `RuntimeString`s the mechanism predicts. |
| 2 | `compiler/src/plugin_manifest.rs` `ensure_manifest_loaded` | **Per-call deep clone.** Returned `PluginManifestCache` **by value**, i.e. `cache.clone()`: the whole `Vec<PluginEntry>` (each with nested `Vec<String>` function lists and class/method tables), the `HashSet<String>` of every registered symbol, and the `HashMap<String, String>` symbol->library index. `try_call_dynamic` calls into it **twice per dynamic SFFI dispatch** (`manifest_error()` then `library_for_symbol()`), so any installed plugin manifest imposed two full O(manifest) deep clones on every extern call. | `ensure_manifest_loaded_borrows_the_cache_instead_of_cloning_it` compares the address of `guard.manifest` against the address inside the global `PLUGIN_MANIFEST_CACHE`. Exact and deterministic — a clone cannot share an address with the original. | Return `MutexGuard<'static, PluginManifestCache>` and borrow through it. Added `manifest_ok()` (allocation-free predicate) for the hot path; `manifest_error()` still clones but is now only reached on the cold failure branch. `registered_plugin_symbols()` keeps its clone — it is called once, at interpreter startup. | 2 deep clones/call -> 0 |
| 3 | `compiler/src/interpreter_extern/dynamic_sffi.rs` `call_fptr` | **Per-call heap allocation.** `let args: Vec<i64> = ...collect()` allocated a `Vec` on **every** dynamic SFFI call, despite the arity being hard-capped at 13 by the `match nargs` transmute arms immediately below. | `call_fptr_dispatches_at_the_arity_cap_and_rejects_one_over` pins both ends of the cap that makes the fixed array sound (13 args dispatches and sums correctly; 14 is rejected with the arity error). `over_arity_call_still_reports_an_inadmissible_argument_first` pins that the rewrite did not change error precedence. | Marshal into a fixed `[i64; MAX_DYNAMIC_SFFI_ARGS]` stack array, with the arity bound-check hoisted above marshalling — and the pre-existing "does not admit argument type" error still reported first for an over-arity call carrying a bad argument. | 1 heap alloc/call -> 0 |
| 4 | `compiler/src/interpreter_extern/sffi_array.rs` `rt_array_concat_fn` | **Three allocations where two suffice.** The left side was cloned into a `Vec` at exactly its own length, the right side was materialised into a *second* full `Vec`, then `items.extend(right_items)` reallocated the destination (its capacity was exact-fit) and threw the intermediate away. | Covered by the existing `rt_array_concat` tests for semantics; the mechanism is visible in the diff (one `Vec::with_capacity(left + right)` plus two `extend_from_slice`, no intermediate). | Borrow both sides where the representation allows (`Value::Array`/`FrozenArray`/`FixedSizeArray`), size the destination once, and `extend_from_slice` twice. Only the packed byte-array representation still materialises, because it must be expanded to `Value`s. | 3 allocs + 1 realloc -> 1 alloc |

## Checked and found CLEAN (no change made)

- **`sffi_return_contract` is not per-call parsing.** It matches on the already-parsed `Type` AST (`Type::Optional`, `Type::Generic{..}`, empty `Type::Tuple`) and does two `&str` equality tests against `"()"` / `"Option"` / `"Optional"`. No string formatting, no type re-parsing, nothing to memoize on the function id. Error messages are `format!`ted only on the error branches.
- **Array/bytes growth is not zero-slack.** `rt_array_push_grow`, `rt_typed_bytes_u8_push` and the sibling append helpers in `runtime/src/value/collections.rs` all grow by `(old_cap * 2).max(4)`, i.e. amortized O(1), matching the string-builder fix `8492fe02a0e`. No exact-size realloc found on an append path.
- **Dynamic symbol caches are bounded by the symbol set, not by call count.** `DYNAMIC_RUNTIME.symbols`, the satellite tables and the manifest tables are keyed by function name and insert at most one entry per distinct symbol (misses are cached as `0`), so they cannot grow per call.
- **`rt_string_len_fn` / `rt_string_to_int_fn` / `rt_string_data_fn`** already special-case `Value::Str` without allocating a runtime string.

## Measured evidence (2026-08-21)

```
rt_string_eq over 20000 x 4096B: pre-fix mechanism grew RSS by 158 MB, post-fix by 0 MB
```

The per-call figure (~8.3 KB) matches the predicted mechanism exactly — two
`alloc_runtime_string` allocations of `size_of::<RuntimeString>() + 4096` each —
which is what makes this a mechanism pin rather than a coincidental RSS
threshold. Defects 2, 3 and 4 are pinned structurally (address identity, arity
cap, allocation count in the diff) rather than by timing, because each removes a
fixed small allocation per call whose cost is below the noise floor of a
wall-clock micro-benchmark on this shared host, while being unambiguous in the
mechanism.

## Validation

- `cargo test -p simple-compiler --release --lib -j8` — 3758 passed, 54 failed. All 5 new tests pass. The 54 are **not** a regression from these fixes: the working tree carries another lane's in-flight edits to `src/runtime/runtime_native.c` and `src/runtime/runtime.h`, which is what the crypto failures (`pbkdf2::dispatch_sha256_c4096`/`sha384`/`sha512` all returning `""`, both `signatures::ed25519_sign_*`) and `rt_string_ends_with_is_registered_and_correct` come from. None of the 54 touches `rt_string_eq`, `rt_array_concat`, `plugin_manifest`, or `call_fptr`; each failing assertion was read individually rather than inferred from the count.
- `cargo test -p simple-runtime --release --lib` — no new failures vs the 10-failure baseline.
- Specs: `import_admission_critical`, `enum_payload_capture`, `multiline_lambda_body`, `non_optional_nil_return_contract`, `duplicate_typed_arg_signature_nil_miss`. **Scope caveat, stated rather than glossed:** `bin/simple` is the deployed JIT'd seed and was deliberately NOT redeployed, so these specs exercise a binary that does not contain these fixes. They are a tree-level regression check, not validation of this change; validation of the change itself is the cargo evidence above.
- `sh scripts/check/check-non-optional-nil-return.shs` — PASS.
