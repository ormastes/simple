# Interpreter: a mutating call through a nested place clones the whole container per call

- Status: OPEN (2026-09-12) — measured, mechanism located; fix in progress on `work/interp-perf-bugs`
- Found: 2026-09-12, while building the interpreter component scaling spec
  (`test/05_perf/interp/interpreter_component_scaling_spec.spl`)
- Component: seed tree-walk interpreter —
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`
  (`handle_method_call_with_self_update_inner`: Index-receiver branch and the
  general PLACE branch), `interpreter/place.rs` (`updated_root`),
  `interpreter_method/collections.rs` (`handle_array_methods` `"push"` arm)
- Lane: interpreter only (`SIMPLE_EXECUTION_MODE=interpreter`, which is what
  `bin/simple test` runs specs in). JIT is flat on every shape below.

## Summary

The interpreter's copy-on-write value model (`Arc<Vec<Value>>`,
`Arc<HashMap<..>>`, `Arc` object fields, `Arc::make_mut` on write) is
O(1)-amortized only while the container is uniquely owned at the moment of the
write. Two receiver shapes have hand-written paths that keep it unique — a bare
identifier (`xs.push(v)`, MECALL-OWNED `me.method()`) and exactly one field
hop (`self.xs.push(v)`, `try_field_array_mutation_in_place`, 2026-08-21).
Every other mutating receiver falls to a path that evaluates the receiver to a
**temporary copy** (an `Arc` clone, refcount 2), mutates the copy, and rebuilds
the root (`updated_root`). With refcount 2 `Arc::make_mut` deep-copies the
entire backing store on every call, so a loop of n mutations is O(n^2).

## Evidence (deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, built 2026-09-06 09:59, 50,093,192 bytes; interpreter lane; 4x n)

| shape | n=20000 | n=80000 | ratio | note |
|---|---:|---:|---:|---|
| `self.inner.xs.push(x)` (method body) | 1.71 s | 22.66 s | 13.3 | nested field, array mutator |
| `rows[i % 4].push(i)` (local) | 0.49 s | 5.80 s | 11.8 | `ARR_MUT_COW_CLONES=20000`, `ARR_MUT_COW_ELEMS_CLONED=49,990,000` at n=20000 |
| `self.rows[r].push(x)` (method body) | 0.57 s | 6.12 s | 10.7 | field + index |
| `self.d.insert(k, v)` (method body) | 8.37 s | >90 s | >10 | dict mutator via field; `self.d[k] = v` is 0.10 s / 0.37 s |
| `self.inner.d[k] = v` (method body) | 8.34 s | >90 s | >10 | 2-level ASSIGNMENT; 1-level is linear |
| `arr[i].inc()` with `arr.len() == n` | 17.58 s | >90 s | >5 | outer array `(*arr).clone()` per call |
| `self.inner.xs.extend([x])` (method body) | 3.60 s | 65.52 s | 18.2 | nested field, same kernel; 1-hop `self.xs.extend(..)` is linear |
| `self.inner.xs.remove(self.inner.xs.len() - 1)` (method body) | 0.38 s @5k | 4.64 s @20k | 12.2 | last element, so `Vec::remove` shifts nothing — the growth is the receiver copy alone |
| `self.items.push(x)` (1 hop) | 0.13 s @30k | | | control — fixed 2026-08-21 |

Linear controls at the same n (ratio 3.0–4.3): local dict insert, `s = s + "x"`,
closure capture, `arr[i].x = v`, `s.slice(i, i+1)`, `char_code_at`, dict get,
plain fn call.

The last two rows were confirmed after the first six and are the same defect,
not new ones: every `ARRAY_MUTATING_METHODS` member reached through a nested
place pays the receiver copy, so `push`/`extend`/`remove`/`insert`/`pop`/`clear`
are all affected; `extend` and `remove` are listed because they were measured.
Both also report all-zero perf counters, for the reason below.

`SIMPLE_PERF_COUNTERS=1` is silent for the nested-field, dict-field, 2-level
assignment and `arr[i].inc()` shapes: those paths carry no counter, which is
why they were never seen — only the Index-receiver array push is instrumented
(and it reports the 49,990,000 cloned elements above).

## Mechanism

- Index receiver (`arr[i].method()`, patterns.rs "Index receiver write-back
  (bug #28)"): `env.get(arr_name).cloned()` aliases the outer `Arc`, then
  `(*arr).clone()` copies the outer `Vec` on every call (O(outer)); for an
  inner ARRAY element it binds the element to a `__indexed_elem_<name>__` temp,
  so the inner `Arc` is held twice and the push deep-copies it (O(inner)).
- General PLACE receiver (`a.b.c.m()`): `evaluate_method_call_with_self_update`
  runs on a copy of the resolved place, then `updated_root` rebuilds the root —
  the copy holds the second reference for the whole call.
- Dict field (`self.d.insert(k, v)`): `try_field_array_mutation_in_place`
  admits ARRAY fields only (`Some(Value::Array(_)) => {}`), so a dict field
  falls through to the general path above.
- 2-level assignment (`self.inner.d[k] = v`): `write_place` → `project_mut` →
  `step_mut` already `Arc::make_mut` per hop, so something upstream holds an
  alias; site pinned in the fix lane (see the site table in the PR).

The identifier fast path is not affected and must stay as is.

## Fix direction (one kernel, not a fifth branch)

`resolve_place(receiver)` → `env.get_mut(root)` → `project_mut` (already
`make_mut` per hop) → mutate the LEAF in place: array mutators via
`apply_array_mutation_in_place`; dict mutators on `Arc::make_mut(entries)`;
a user class method on a nested object by evaluating args first (MECALL-OWNED
rule), `mem::replace`-ing the slot, running with owned `self`, and storing the
result back. Route the Index-receiver and general PLACE branches through it.
Aliasing semantics are unchanged because `make_mut` still copies when a second
binding genuinely holds the `Arc` — pinned by the "value semantics preserved"
`describe` in the scaling spec and by Rust unit tests beside
`genuinely_aliased_field_array_still_copies_on_write`.

## Fix-test spec

`test/05_perf/interp/interpreter_component_scaling_spec.spl` — one `it` per
shape, ratio bound `4x n < 7x time`, result asserted so a fix that drops writes
fails; second `describe` pins copy-on-write for aliased containers.

## Related

- `string_builder_interpreter_push_worse_than_quadratic_2026-08-18.md` (the
  1-hop instance of the same defect; resolved 2026-08-21/22)
- `doc/03_plan/agent_tasks/simple_infra_optimization_parallel_plan_2026-09-08.md` (L2/L3)
