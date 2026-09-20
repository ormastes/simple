# BUG: `rt_file_stat` returns the file SIZE on the interpret lane, so `file_modified_time` answers a byte count

- **id:** rt_file_stat_returns_size_on_interpret_lane_2026-09-19
- **status:** FIXED 2026-09-19 (in source; `bin/simple` not yet redeployed with it)
- **severity:** P1 — a silent wrong answer on the default lane for `bin/simple test`, with a measured production casualty
- **found:** 2026-09-19, while chasing a `FAIL` from `check-doctest-manifest-staleness.shs`

## Symptom

`file_modified_time(path)` returns the file's **size in bytes** instead of its
modification time — on the **interpret lane only**. No error, no warning.

Measured on the deployed seed, for a 10-byte file:

| lane | `file_size` | `file_modified_time` |
|---|---|---|
| default (JIT) | 10 | `1789803583` — a correct epoch |
| `SIMPLE_EXECUTION_MODE=interpret` | 10 | **`10`** — the size |

Both lanes ran the same source, through the same import
(`std.nogc_sync_mut.io.file_ops`). Only the lane differed.

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`:

```rust
/// Get file stat info (simplified - returns size or -1)
pub fn rt_file_stat(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::metadata(&path) {
        Ok(meta) => i64::try_from(meta.len())          // <-- the SIZE
            .map(Value::Int)
            .map_err(|_| CompileError::runtime("rt_file_size exceeds i64 range")),
        Err(_) => Ok(Value::Int(-1)),                  // <-- contract says 0
    }
}
```

It was a byte-for-byte duplicate of `rt_file_size` sitting two functions below
it, down to a copy-pasted `"rt_file_size exceeds i64 range"` error string. The
doc comment said so out loud — *"simplified - returns size or -1"* — which is
presumably why it was never questioned: it looked deliberate.

The contract it was supposed to meet is not ambiguous. **Both** C runtime
implementations return the mtime and use **0**, not -1, as the failure value:

- `src/runtime/runtime.c:2369` → `return (int64_t)st.st_mtime;` / `return 0;`
- `src/runtime/runtime_core_host_services.c:107` → `stat(...) == 0 ? (int64_t)metadata.st_mtime : 0`

And the pure-Simple caller agrees — `file_modified_time` in
`src/lib/nogc_sync_mut/io/file_ops.spl:237` calls `rt_file_stat` and documents
*"A zero result fails closed: cache users must treat it as unavailable."*

So the interpreter was wrong on both the value **and** the sentinel.

## Why nothing caught it

It is wrong on one lane only. The JIT and native lanes link the C function and
have always answered correctly, so the two engines silently disagreed and every
JIT-lane probe said "fine". That is how the first investigation in this session
went wrong: `file_modified_time` was probed through `bin/simple run` — the JIT
default — pronounced correct, and the real defect was very nearly filed as
"stale local cache".

No spec covered it either. `grep` over `test/` finds no spec for
`file_modified_time` at all.

## The casualty, measured

`bin/simple test` runs specs on the **interpret** route. The test-manifest
scanner (`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`) calls
`file_modified_time` for every discovered spec and writes it as the `mtime`
column, so every row of `.simple/test-manifest.idx` was written with
`mtime == size`:

```
FAIL  manifest-columns: all 11629 row(s) have size == mtime -- size-only invalidation fingerprint
```

`manifest_entry_fingerprint_matches` requires **both** `file_size` and
`file_mtime` to match before it reuses a cached entry. With mtime carrying a
copy of the size, the fingerprint degrades to size-only: **a same-size edit to a
spec never invalidates test discovery**, so a changed spec can be served from
the manifest as unchanged.

Deleting the manifest does not help, and trying that is what proved the defect
was live rather than historical: a fresh scan of `test/01_unit/interpreter`
rewrote 7 of 7 real rows with `mtime == size` again.

## The fix

`rt_file_stat` now returns modification time in seconds since the Unix epoch,
and returns `0` on failure, matching both C implementations. The extraction
reuses the pattern already present in this same file for the `StatHandle`
path (`meta.modified()` → `duration_since(UNIX_EPOCH)` → `as_secs()`), rather
than inventing a second one.

## Evidence

| check | before | after |
|---|---|---|
| `file_modified_time` on a 10-byte file, interpret lane | **10** | **1789803583** |
| same, JIT lane | 1789803583 | 1789803583 (**lanes now agree**) |
| `file_modified_time_spec.spl` (new) | 1 passed, **3 failed** | **4 passed, 0 failed** |
| `nested_fn_in_lambda_capture_spec` | 8/8 | 8/8 |
| `optional_unwrap_payload_spec` | 11/11 | 11/11 |
| `mutate_through_index_shapes_spec` | 7/7 | 7/7 |
| `variadic_method_params_spec` | 9/9 | 9/9 |
| `check-deployed-binary-optional-unwrap.shs` | PASS | PASS |

The new spec's first example is a **control** that asserts the fixture really is
10 bytes. It passes on the broken binary, so a fixture mistake cannot masquerade
as the defect — only the three mtime assertions move. This spec genuinely
discriminates, because the defect lives on the interpret route that
`bin/simple test` uses; the JIT-only defects in this tree cannot be guarded this
way.

## Not fixed here

`rt_file_stat_mtime` and the `rt_stat_open`/handle family are untouched and were
already correct. The 803 stale `/tmp/tmp.*/shard.N/specs` rows that
`check-doctest-manifest-staleness.shs` also reports are genuine local-cache
garbage from earlier sharded runs and clear on regeneration — that part really
was stale state, and is unrelated to this defect.

## Related

- `seed_jit_optional_unwrap_returns_enum_box_2026-09-18` — the mirror image:
  correct on interpret, wrong on JIT. Together they are the argument for probing
  **both** lanes before pronouncing a builtin correct.
- `nested_fn_in_spec_block_loses_captured_local_2026-08-04` — same session; also
  a defect that only one lane could see.
