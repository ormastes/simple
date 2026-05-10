# Phase-4 Spec Summary — Semantic Deduplication

Generated: 2026-04-28
Phase-5 (implement) must clear ALL tests in these files.

---

## A1 — Loader unload delegation

**Spec file:** `test/unit/compiler/loader/module_loader_spec.spl`
(extended — 9 new `it` blocks appended after the existing reload test)

**Call sites covered:**
- `src/compiler/99.loader/module_loader.spl:153–191` — `me unload` (impl-method, 38-line body)
- `src/compiler/99.loader/module_loader.spl:304–341` — `me moduleloader_unload` (free-function, reference)

**Boundary cases exercised:**
- Unload of a never-loaded path (no-op, no panic)
- Double-unload idempotency (second call is silent no-op)
- Unload clears `loader.modules` entry
- Unload drops global symbols owned by the module
- Unload clears `jit.loaded_metadata` for the path
- Unload clears `jit.jit_cache` entries for the module's symbols
- Unload preserves global symbols owned by a *different* module
- Parity test: impl-method path and free-function path produce identical `modules`, `global_symbols`, and `global_symbols.len()` after unload
- Unload after JIT symbols were resolved through `moduleloader_resolve_symbol`

**Run mode:** interpreter (per `feedback_compile_mode_false_greens`)

---

## B1 unit — BTreeMap/BTreeSet FFI macro parity

**Spec file:** `test/unit/lib/nogc_async_mut/btreemap_spec.spl`
(new file)

**Call sites covered (via the FFI layer backed by these C files):**
- `collections.c:1–15` — TAG_MASK, ENCODE_INT, IS_INT, IS_HEAP, NIL_VALUE
- `hashmap.c:27–46` — TAG_MASK, ENCODE_INT, IS_INT, IS_HEAP (subset)
- `primitives.c:27–52` — full macro set + HeapHeader, RuntimeString, RuntimeArray
- `rt_extras.c:34–51` — full macro set + HeapHeader, RuntimeString

**Boundary cases exercised:**
- Empty map/set initial state
- insert returns true; len increments
- get/contains_key after insert
- remove of existing key (len decrements, key gone)
- remove of non-existent key (no-op, no panic)
- double-insert same key (last value wins, len stays 1)
- 32-entry stress insert (exercises BTree node splits)
- first_key / last_key reflect lexicographic sorted order
- clear then re-insert works
- keys() / values() / entries() return non-nil for non-empty map
- BTreeSet: all of the above analogues
- hashmap.c cross-check: integer values stored via btreemap still decode correctly

**Run mode:** interpreter (per `feedback_compile_mode_false_greens`)

---

## B1 boot — BTreeMap QEMU smoke test

**Spec file:** `examples/simple_os/arch/x86_64/btreemap_test_entry.spl`
(new file)

**Call sites covered:**
- `collections.c:1–15` — ENCODE_INT, IS_HEAP, DECODE_PTR (via btreemap value decode at boot)
- `hashmap.c:27–46` — IS_INT, TAG_MASK (via hashmap macro cross-check section)
- `primitives.c:27–52` / `rt_extras.c:34–51` — HeapHeader, RuntimeString struct access

**Boundary cases exercised:**
- btreemap new → empty state
- 3-entry insert + lookup + first_key + last_key
- remove of existing key
- remove of non-existent key (no crash)
- double-insert last-value-wins
- 32-entry stress insert + spot-check + clear + re-insert
- btreeset: insert / contains / remove / first / last / dup-insert idempotent
- hashmap.c macro cross-check: integer keys encoded with ENCODE_INT decode correctly through btreemap (IS_INT/IS_HEAP cross-tag validation)

**Run gate:** `sh scripts/check-freebsd-bootstrap-qemu.shs --smoke`
Failure detection: QEMU stdout scanner looks for "FAIL:" prefix printed by the `check()` helper.

---

## C1+C2 — Cranelift call_runtime helpers

**Spec file:** `src/compiler_rust/compiler/tests/call_runtime_helpers.rs`
(new file)

**Call sites covered:**
- C1: `methods.rs` private `call_runtime_1/2/3/2_void` (promoted to `helpers.rs pub(crate)`)
- C1: ~74 open-coded `runtime_funcs[name] + declare_func_in_func + adapted_call` sites across 17 files
- C2: `calls.rs:698`, `methods.rs:309`, `closures_structs.rs:65`, `mod.rs:232` — dynamic-resolve pattern → `declare_uniform_i64_import`

**Boundary cases exercised:**
- All 5 arity variants importable as `pub(crate)` (compile-time check)
- Arity-0: no-arg runtime call path (array.len() proxy)
- Arity-1: single-arg call path (array pop/clear/keys proxy)
- Arity-2: two-arg call path (string concat proxy)
- Arity-2 void: no-return call path (array push proxy)
- Arity-3: three-arg call path (array/dict set proxy; accepts clean error if not wired up yet)
- C2 idempotency: `declare_uniform_i64_import` called twice with same name → no panic, no duplicate-declaration error
- C2 zero-param boundary: uniform import with 0 parameters
- C2 three-param boundary: uniform import with 3 parameters
- Regression canaries: array push/pop, string concat, dict operations — must still pass post-merge

**Perf gate (AC-3):** Separate harness documented in `arch.md §4`. Measure `bin/simple build` via `/usr/bin/time -v`. Median of 3 warm runs. ≥3% wall-clock or RSS regression blocks the C1+C2 commit.

**Run mode:** `cargo test` in `src/compiler_rust/compiler/`

---

## D1 — lower_call_args HIR lowering helper

**Spec file:** `src/compiler_rust/compiler/tests/hir_lower_call_args.rs`
(new file)

**Call sites covered:**
- `calls.rs:47`  — enum-ctor path `Some(x)` / `Ok(x)` / `Err(x)` inline loop
- `calls.rs:70`  — struct-init from known type (`fields_hir` loop)
- `calls.rs:89`  — struct-init lenient / named-arg uppercase (`fields_hir` loop)
- `calls.rs:194` — regular function call fallthrough (`args_hir` loop)
- `mod.rs:272`   — `lower_method_call` generic path (`hir_args` loop)
- `mod.rs:386`   — `lower_method_call` second path (`hir_args` loop)
- `simd.rs:240`  — `lower_static_method_call` (`args_hir` loop)

**Boundary cases exercised:**
- Zero-argument function call (calls.rs:194 boundary)
- Single-argument call
- Three-argument call
- Named args: `arg.name` is silently dropped; only `arg.value` is lowered (parity test for named-target calls)
- Single named-arg boundary
- Error propagation: undefined callee must not panic (inner `lower_expr` failure)
- `lower_builtin_call` delegation parity: `print(msg)` still produces 1-arg BuiltinCall
- All 7 call sites parity table: each compiled independently; arg-count in HIR matches expected value pre- and post-merge

**Spec gaps recorded in:** `.sstack/semantic-dup-removal/spec_gaps.md`
(sites that require full compiler context — marked `[SPEC-GAP]` in test output, not hard failures)

**Run mode:** `cargo test` in `src/compiler_rust/compiler/`

---

## Files written in Phase 4

| File | Status | Cluster |
|------|--------|---------|
| `test/unit/compiler/loader/module_loader_spec.spl` | Extended (+9 `it` blocks) | A1 |
| `test/unit/lib/nogc_async_mut/btreemap_spec.spl` | New | B1 unit |
| `examples/simple_os/arch/x86_64/btreemap_test_entry.spl` | New | B1 boot |
| `src/compiler_rust/compiler/tests/call_runtime_helpers.rs` | New | C1+C2 |
| `src/compiler_rust/compiler/tests/hir_lower_call_args.rs` | New | D1 |
| `.sstack/semantic-dup-removal/spec_summary.md` | New | — |
| `.sstack/semantic-dup-removal/spec_gaps.md` | New | — |
