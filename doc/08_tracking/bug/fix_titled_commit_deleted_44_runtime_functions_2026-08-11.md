# A "fix"-titled commit deleted 44 runtime functions and broke the build (2026-08-11)

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Offending commit:** `6e2f613d302` "fix(runtime): preserve u64 across erased values"
  (cherry-pick of `5f3066c9ca3`), parent `28eaee006ab`.
- **Inherited by:** `ad2b5d5307f` (a *legitimate* revert of an unrelated 427-file
  bulk deletion). It restored the tree to the `6e2f613d302` state and therefore
  INHERITED this break; it did not cause it and must not be reverted.

## Symptom

`cargo build --release --bin simple` fails in `simple-runtime`:

```
error[E0432]: unresolved imports `value::rt_array_each`, `value::rt_array_map`,
  `value::rt_array_reduce`, `value::rt_map`, `value::rt_value_unbox_int`
error[E0432]: unresolved imports `value::rt_tls_client_connect_address_with_sni_timeout`,
  `value::rt_tls_client_read_timeout`, `value::rt_tls_client_write_timeout`
```

`runtime/src/lib.rs` still re-exported names whose definitions/re-exports the
commit had removed.

## Root cause

`6e2f613d302` carried a genuine, well-tested `WideInt -> UInt` u64 rework in
`value/{core,heap}.rs` and `value/sffi/{equality,value_ops,io_print}.rs`, but the
same commit also wrote **stale-snapshot content** over two files:

| file | delta vs parent | effect |
|---|---|---|
| `value/collections.rs` | -1896 / +109 | **44 `rt_*` functions deleted** |
| `value/mod.rs` | -37 re-export lines | dropped ~40 re-exports (TLS timeouts, `rt_tls13_sha256`, `rt_file_is_char_device`, `rt_array_free_deep`, ~25 `rt_string_*`, `rt_array_each/map/reduce`, `rt_map`, `runtime_env_registry_test_lock`) |

Deleted from `collections.rs`: `rt_push`, `rt_pop`, `rt_sort`, `rt_find`,
`rt_take`, `rt_clear`, `rt_drop`, `rt_reverse`, `rt_reverse_mut`, `rt_map`,
`rt_array_each`, `rt_array_map`, `rt_array_reduce`, `rt_array_remove`,
`rt_array_free_deep`, `rt_collection_remove`, and 28 `rt_string_*`
(`pad_left/right`, `partition`, `rpartition`, `title`, `zfill`, `squeeze`,
`substr`, `substr_from`, `repeat`, `replace_first`, `swapcase`, `capitalize`,
`center`, `chomp`, `char_count`, `find_all`, `is_alnum`, `is_alpha`, `is_digit`,
`is_whitespace`, `sorted`, `split_limit`, `remove_prefix`, `remove_suffix`,
`trim_start_matches`, `trim_end_matches`, `new_uncached_untracked`). It also
reverted `rt_array_all` from the 2-arg predicate form back to a 1-arg form.

Collateral deletions in the u64 rework itself (real regressions, not build
breaks): `rt_native_cmp` (JIT ordering fallback, still emitted by codegen),
`rt_value_unbox_int` (still emitted by Cranelift), the text-decode branch of
`rt_value_as_int` (the `char_at` cast fix), and the loud
`rt_value_raw_i64` heap-truncation guard plus its subprocess test.

Finally the rename left one consumer behind: `value/sffi/io_print.rs:478` still
said `HeapObjectType::WideInt` -> E0599.

## Fix

Union restore, not a choice of sides:

- `value/collections.rs`, `value/mod.rs`: restored from parent `28eaee006ab`,
  then re-applied the genuine u64 work (`WideInt` -> `UInt` rename,
  `as_heap_u64` prelude in `compare_runtime_values`, `as_heap_u64() == Some(0)`
  falsy checks in `rt_array_all_truthy`/`rt_array_any_truthy`) and the new
  re-exports (`rt_value_u64`, `rt_value_as_u64`, `rt_unwrap_or_value`,
  `rt_expect_or_trap`).
- `value/sffi/value_ops.rs`: kept the new `rt_value_u64`/`rt_value_as_u64` and
  the u64 boundary tests; restored `rt_value_unbox_int` (now u64-aware), the
  `rt_value_as_int` text-decode branch, the `rt_value_raw_i64` panic guard, and
  `raw_i64_guard_tests`.
- `value/sffi/equality.rs`: kept the whole u64 rework; restored `rt_native_cmp`.
- `value/sffi/io_print.rs`: `WideInt` -> `UInt`, printing via `as_heap_u64()`.

Superset proof (`grep -oE 'fn rt_[a-z_0-9]+' | sort -u` over
`src/compiler_rust/runtime/src`):

| tree | distinct `rt_*` fns |
|---|---|
| parent `28eaee006ab` | 1961 |
| origin/main (broken) | 1919 |
| **restored** | **1965** |

`comm -23` against both inputs is empty — the result is a strict superset of
each. The 4 net-new names are `rt_value_u64`, `rt_value_as_u64`,
`rt_unwrap_or_value`, `rt_expect_or_trap`.

## Verification

- `cargo build --release --bin simple` — Finished, exit 0.
- `check-deployed-binary-capabilities.shs` — `PASS — 9 probe(s) checked`.
- `check-native-unwrap-enum-receiver.shs` — `PASS — 8 checked`.
- `cargo test -p simple-compiler --test runtime_symbol_registration_gate` —
  `1 passed`.

## Why the guards missed it

- `check-tree-size-push.shs` bands on ±0.15% of ~112k files; a 2-file content
  change is invisible to it. It is a WIPE detector, not a content detector.
- `check-no-revert-push.shs` requires >= 5 files reverting to the SAME prior
  commit; this was 2 files, and the content was a stale snapshot rather than an
  exact prior blob.
- The commit title said `fix(runtime)`, and the u64 half of it was real, so a
  title/diffstat skim read as legitimate.

## Recommendations

1. **`check-seed-builds-push.shs` (the new sixth guard) is the right gate** —
   it compiles the seed over the outgoing range and would have caught the
   E0432/E0599 directly. Keep it mandatory in the pre-push set.
2. **Add a runtime-symbol-count regression check.** A cheap fail-closed guard:
   count `grep -oE 'fn rt_[a-z_0-9]+' src/compiler_rust/runtime/src | sort -u`
   for BASE and NEW; FAIL when NEW loses any name that BASE had unless the
   commit message lists the removals explicitly. A build gate only catches
   removals that break a re-export; the 28 `rt_string_*` functions here were
   also dropped from `mod.rs`, so a symbol-count guard is what catches the
   silently-unexported half.
3. Treat any commit whose diffstat shows a single file at >10x the deletion
   count of every other file in the same commit as a stale-snapshot candidate,
   regardless of title.
