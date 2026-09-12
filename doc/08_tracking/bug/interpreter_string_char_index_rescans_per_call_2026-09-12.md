# Interpreter: `substr` / `char_at` / `s[i]` rescan the whole string on every call

- Status: RESOLVED (2026-09-12) on `work/interp-string-index` — ratios 14.58/8.44/8.36 -> 3.99/4.00/4.00 at 4x n; pinned by test/05_perf/interp/string_char_index_scaling_spec.spl and STRIDX rows in scripts/check/check-perf-regression-tests.shs
- Found: 2026-09-12, interpreter component scaling probes
- Component: seed tree-walk interpreter —
  `src/compiler_rust/compiler/src/interpreter_method/string.rs` (`"substr"`,
  `"char_at" | "at"`), `interpreter/expr/collections.rs`
  (`indexed_string_char`)
- Lane: interpreter only; JIT/native call `rt_string_substr` /
  `rt_string_char_code_at` and are flat.

## Summary

`char_code_at` got an ASCII memo fast path (`shared_text_is_ascii`,
`interpreter_method/mod.rs`) because `s.chars().nth(i)` made
`while i < s.len(): s.char_code_at(i)` O(n^2). The three sibling accessors
never got it:

- `substr(start, len)`: `let chars: Vec<char> = s.chars().collect();` —
  allocates and walks the ENTIRE string per call, regardless of `len`.
- `char_at(i)` / `at(i)`: `s.chars().nth(idx)` — O(i) per call.
- `s[i]` (`indexed_string_char(s: &str, ..)`): `s.is_ascii()` rescans the
  whole string per call before the byte fast path; it takes `&str`, so the
  `Arc`-keyed memo cannot apply.

## Evidence (deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, built 2026-09-06 09:59; interpreter lane; ASCII text of n bytes built by `join`)

| loop body | n=20000 | n=80000 | ratio (linear = 4) |
|---|---:|---:|---:|
| `s.substr(i, 1)` | 0.88 s | 12.81 s | 14.6 |
| `s.char_at(i)` | 0.10 s | 0.63 s | 6.3 |
| `s[i]` | 0.09 s | 0.59 s | 6.6 |
| `s.slice(i, i + 1)` (control, byte-indexed) | 0.08 s | 0.28 s | 3.5 |
| `s.char_code_at(i)` (control, memoised) | 0.07 s | 0.24 s | 3.4 |

## Fix direction (semantics unchanged)

Gate on `shared_text_is_ascii(&Arc<String>)` exactly as `char_code_at` does:
ASCII → byte slice / byte index; otherwise walk `char_indices()` to `start`
and take `len` characters (O(start + len), no `Vec<char>`). Thread the
`Arc<String>` into `indexed_string_char` so the memo applies. Keep the
`eval_arg_usize` saturation, the negative-index rules and the out-of-bounds
error text byte-identical.

## Fix-test spec

`test/05_perf/interp/string_char_index_scaling_spec.spl` — ratio bound per
accessor plus non-ASCII correctness pins.

## Related

- `interpreter_nested_place_mutation_clones_container_2026-09-12.md` (same
  session, different mechanism)
- `doc/03_plan/agent_tasks/simple_infra_optimization_parallel_plan_2026-09-08.md`
  ("L2 char_code_at cursor source reconciliation" — the pure-Simple
  `core_string.spl` cursor is the self-hosted twin of this fix)
