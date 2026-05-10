# Phase-3 Architecture: Semantic Deduplication

**Date:** 2026-04-28
**Clusters approved:** A1, B1, C1, C2, D1
**Phase 5 execution order:** A1 → B1 → D1 → C1 (C2 ships in C1 commit — same file, same owner)

---

## 1. Cluster Summary Table

| ID | Scope | Helper name & signature | Location (file:where) | LOC delta estimate |
|----|-------|-------------------------|-----------------------|--------------------|
| A1 | `src/compiler/99.loader/module_loader.spl` | `moduleloader_unload(self, path: text)` — already exists as free function | Same file — `me unload` body replaced by single delegator line | −37 |
| B1 | `examples/simple_os/arch/x86_64/boot/{collections,hashmap,primitives,rt_extras}.c` | No new helper — `baremetal_runtime.h` already canonical | Delete inline macro blocks, add `#include`; 4 files | −78 (approx: 15+20+26+17) |
| C1 | `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` | `call_runtime_0`, `call_runtime_1`, `call_runtime_2`, `call_runtime_2_void`, `call_runtime_3` — promote from private `methods.rs` + add `call_runtime_0` | `helpers.rs` (new pub(crate) section) + delete from `methods.rs` | −~130 (74 open-coded sites × ~3 lines saved each, net of ~30 lines added to helpers.rs) |
| C2 | `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` | `declare_uniform_i64_import<M: Module>(ctx, builder, name, n_params) -> FuncRef` | `helpers.rs` (new function below C1 helpers) | −~40 (4 sites × ~12 lines saved each, net of ~12 lines added) |
| D1 | `src/compiler_rust/compiler/src/hir/lower/expr/helpers.rs` | `lower_call_args(&mut self, args: &[ast::Argument], ctx: &mut FunctionContext) -> LowerResult<Vec<HirExpr>>` | `helpers.rs` (new method on `Lowerer`) | −~21 (7 sites × 4 lines saved each, net of +7 lines added) |

**Total estimated LOC delta: −306** (see Section 7 for exact sum).

---

## 2. Cross-Cluster Sequencing

**Order: A1 → B1 → D1 → C1+C2**

**Reasoning:**

- **A1 first** — single-file change in Simple source, one-line body swap. Lowest blast radius of all clusters. No Rust rebuild required. Validates the pipeline rhythm before touching C or boot-path code.
- **B1 second** — boot C files, mechanical `#include` replacement. No algorithm change. Must happen before any Cranelift work to keep scopes disjoint. Requires QEMU smoke test to confirm no boot regression.
- **D1 third** — one new method in `hir/lower/expr/helpers.rs`, 7 call-site rewrites in the same crate. All within `src/compiler_rust/compiler/src/hir/lower/expr/`. No overlap with the Cranelift instr scope (C). Independently verifiable with existing HIR lowering tests before C1 changes the hot codegen path.
- **C1+C2 last** — largest blast radius (74+ sites, 17 files, hot codegen path, perf measurement required). Ships as **one commit** (C1 helpers + C2 helper added to helpers.rs, all callsite rewrites). Internal work order is: C1a (add helpers to helpers.rs, delete from methods.rs), then C1b (rewrite callsites), then C2 (add declare_uniform_i64_import, rewrite its 4 callsites) — but this is all ONE commit per AC-4.

**C1/D1 independence verified:**
- `src/compiler_rust/compiler/src/hir/lower/expr/helpers.rs` contains only `lower_builtin_call`, `lower_gpu_dim_arg`, `parse_swizzle_pattern` — no `call_runtime_*`, no `declare_func_in_func`, no Cranelift imports. D1 adds `lower_call_args` to this file, which has zero overlap with C1's `helpers.rs` in `codegen/instr/`.
- `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` contains only `get_vreg_or_default`, `create_string_constant`, `fnv1a_hash`, `declare_named_bytes`, `create_cstring_constant`, `adapted_call` — no HIR types. C1 adds `call_runtime_*` here; no interaction with D1.
- **D1 does not depend on C1.** The two helpers.rs files are in different crates, different modules, different import namespaces. They can proceed sequentially in any order.

---

## 3. Per-Cluster Design

### A1 — `me unload` delegates to `me moduleloader_unload`

**Owner file:** `src/compiler/99.loader/module_loader.spl`

**Final helper signature:** `me moduleloader_unload(self: ModuleLoader, path: text)` — already exists at lines 304–341. No new function. `me unload` becomes the one-line delegator:

```simple
me unload(path: text):
    moduleloader_unload(self, path)
```

**Visibility:** `me` (Simple instance method convention) — no change to `moduleloader_unload`'s existing visibility.

**Migration steps:**
1. Replace the body of `me unload` (lines 153–191, 38 lines) with the single delegator line above.
2. Confirm the file compiles: run `bin/simple build lint` on the loader scope.
3. Add the intensive test case (see Section 5).
4. Run full test suite; confirm `module_loader_spec.spl` and `module_loader_crash_fix_spec.spl` stay green.
5. Commit (one commit: "refactor(loader): me unload delegates to moduleloader_unload").

**Behavioural-equivalence claim:** `me unload` and `moduleloader_unload` are identical 38-line bodies (verified by text diff in Research A). The delegator preserves all mutation effects: `self.modules`, `self.jit.jit_cache`, `self.global_symbols`, `self.jit.loaded_metadata` all mutate identically. Guard condition `if not self.modules.has(path): return` is in `moduleloader_unload` (line 304–306), so double-unload and no-op cases are preserved.

**Rollback plan:** Revert the single-line change to restore the 38-line body verbatim (it is checked in via git; `git show HEAD:src/compiler/99.loader/module_loader.spl` retrieves it). No downstream files are changed.

---

### B1 — Replace tagged-value macro copies with `#include "../../common/baremetal_runtime.h"`

**Owner file:** `baremetal_runtime.h` at `examples/simple_os/arch/common/baremetal_runtime.h` — already canonical, no edits needed. Changes are deletions + `#include` additions in 4 consumer files.

**Visibility:** C preprocessor macros (no language-level visibility).

**Include order (hard requirement per header's own docstring):**
Each consumer file must have, in this order:
```c
#include <stdint.h>
#include <stddef.h>
// ... any arch-specific static function declarations (serial_putchar etc.) if present ...
#include "../../common/baremetal_runtime.h"
```
`<stdint.h>` and `<stddef.h>` must precede the include because `baremetal_runtime.h` uses `int64_t`, `uint64_t`, `uint32_t`, `uintptr_t`, `size_t` without re-including them. Verified: all 4 consumer files already have `<stdint.h>` and `<stddef.h>` at their tops.

**Migration steps (per file, in order):**

For each of `collections.c`, `hashmap.c`, `primitives.c`, `rt_extras.c`:
1. Identify the inline macro block (TAG_MASK … HeapHeader / RuntimeString / RuntimeArray typedefs).
2. Delete the inline block entirely.
3. Insert `#include "../../common/baremetal_runtime.h"` immediately after the last `<stddef.h>` include line.
4. Check for `RV` typedef alias (`collections.c` uses `typedef RuntimeValue RV;` — keep this line after the include since `baremetal_runtime.h` does not define `RV`).
5. Compile: `bin/simple build` (which exercises the SimpleOS boot C compilation path).
6. Run QEMU smoke test (see Section 4 test plan and Section 5).

**All 4 files in one commit** per AC-4: "refactor(simpleos/boot): replace inline tagged-value macros with baremetal_runtime.h include".

**Behavioural-equivalence claim:** `baremetal_runtime.h` is a strict superset of all four inline blocks. Adding `IS_FLOAT`, `IS_SPECIAL`, `TAG_FLOAT`, `HEAP_BTREESET` etc. to files that previously omitted them is safe — those macros are unused in those files and there are no re-definition conflicts (all definitions are character-for-character identical to the canonical header's definitions).

**Rollback plan:** Revert the 4 consumer files to their git-tracked versions. `baremetal_runtime.h` is untouched, so rollback is a clean 4-file revert.

---

### C1 — Promote `call_runtime_N` helpers to `codegen/instr/helpers.rs`

**Owner file:** `src/compiler_rust/compiler/src/codegen/instr/helpers.rs`

**Final helper signatures (all `pub(crate)`, all `#[inline]`):**

```rust
#[inline]
pub(crate) fn call_runtime_0<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
) {
    let func_id = ctx.runtime_funcs.get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, builder.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[]);
}

#[inline]
pub(crate) fn call_runtime_1<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs.get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, builder.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg]);
    builder.inst_results(call)[0]
}

#[inline]
pub(crate) fn call_runtime_2<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs.get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, builder.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2]);
    builder.inst_results(call)[0]
}

#[inline]
pub(crate) fn call_runtime_2_void<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) {
    let func_id = ctx.runtime_funcs.get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, builder.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[arg1, arg2]);
}

#[inline]
pub(crate) fn call_runtime_3<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
    arg3: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs.get(func_name)
        .unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", func_name, builder.func.name));
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2, arg3]);
    builder.inst_results(call)[0]
}
```

Note: existing `methods.rs` helpers use `ctx.runtime_funcs[name]` (index operator, panics with a less useful message). Replace with `.get().unwrap_or_else(|| panic!(...))` for function-name attribution. All 5 helpers must use this form.

Arity-4+ sites: leave open-coded (anti-over-engineering: fewer than 5 sites, a varargs wrapper adds complexity).

**Visibility:** `pub(crate)` — accessible from all 17 instr/ files.

**Migration steps (internal work order — ONE commit total):**
1. **C1a:** Add the 5 helpers to `helpers.rs` with `pub(crate) #[inline]`. Import `adapted_call` (already in same file). Import `cranelift_codegen::ir::Value` at the top of the new section.
2. **C1a cont.:** Delete the 4 private `call_runtime_*` functions from `methods.rs` (lines 14–68). Update `methods.rs` to import `call_runtime_1/2/2_void/3` from `super::helpers`.
3. **C1b:** Rewrite the ~74 open-coded sites across 17 files to use the helpers. Files affected: `actors.rs`, `async_ops.rs`, `basic_ops.rs`, `body.rs`, `calls.rs`, `closures_structs.rs`, `collections.rs`, `constants.rs`, `contracts.rs`, `core.rs`, `coverage.rs`, `enum_union.rs`, `fields.rs`, `memory.rs`, `parallel.rs`, `pattern.rs`, `pointers.rs`, `result.rs`. Each open-coded site is exactly the 3-line pattern; replace with one `call_runtime_N(...)` call.
4. Run perf measurement (see Section 4) — must pass ≥3% threshold before committing.
5. Run `cargo test` in the compiler crate — all existing tests must pass.
6. Commit: "refactor(cranelift/instr): promote call_runtime_N + declare_uniform_i64_import to helpers.rs".

**Behavioural-equivalence claim:** Each helper is character-for-character equivalent to the open-coded 3-line pattern, with the sole change of upgrading the panic message. `adapted_call` is the same function (already in helpers.rs, already used by methods.rs). `#[inline]` preserves the previous inlining behaviour that was implicit when the helpers were file-local private functions.

**Rollback plan:** `git revert` the single C1+C2 commit. Because all changes are in `src/compiler_rust/compiler/src/codegen/instr/`, the revert is clean and does not touch other crates.

---

### C2 — `declare_uniform_i64_import` helper in `codegen/instr/helpers.rs`

**Owner file:** `src/compiler_rust/compiler/src/codegen/instr/helpers.rs` (same file as C1; ships in same commit)

**Final helper signature:**

```rust
/// Look up or declare an import function with `n_params` I64 params → I64 return.
/// Returns the `FuncRef` for use in the current function body.
/// Caches the `FuncId` in `ctx.func_ids` to avoid Cranelift "incompatible
/// declaration" errors on re-declaration.
/// NOTE: for callers that also need func_addr() after the FuncRef, call
/// builder.ins().func_addr(types::I64, func_ref) at the call site.
#[inline]
pub(crate) fn declare_uniform_i64_import<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    name: &str,
    n_params: usize,
) -> cranelift_codegen::ir::FuncRef {
    use cranelift_codegen::ir::{types, AbiParam, Signature};
    use cranelift_module::{Linkage, Module as _};
    use crate::codegen::shared::platform_call_conv;

    let func_id = if let Some(&existing) = ctx.func_ids.get(name) {
        existing
    } else {
        let mut sig = Signature::new(platform_call_conv());
        for _ in 0..n_params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let id = ctx.module
            .declare_function(name, Linkage::Import, &sig)
            .unwrap_or_else(|_| match ctx.module.get_name(name) {
                Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                _ => panic!("declare_uniform_i64_import: '{}' not a function", name),
            });
        ctx.func_ids.insert(name.to_string(), id);
        id
    };
    ctx.module.declare_func_in_func(func_id, builder.func)
}
```

**Excluded site:** `closures_structs.rs:492–520` (N-1 fallback variant) — leave open-coded. Add a comment at that site pointing to this helper for the common case.

**Call sites:** `calls.rs:698–711`, `methods.rs:309–321`, `closures_structs.rs:65–79`, `mod.rs:232–241`. The `mod.rs` site additionally calls `builder.ins().func_addr(types::I64, func_ref)` after the declare — that one line stays at the call site.

**Migration steps:** Part of the C1+C2 single commit (see C1 step 3 above — after the call_runtime_N rewrites, apply the 4 declare_uniform_i64_import rewrites).

**Behavioural-equivalence claim:** All 4 included sites share the identical 5-step invariant (cache check → sig build → declare_function → insert cache → declare_func_in_func). The helper centralises `platform_call_conv()` so a future CC change is one edit.

**Rollback plan:** Same as C1 — single commit revert covers both.

---

### D1 — `lower_call_args` in `hir/lower/expr/helpers.rs`

**Owner file:** `src/compiler_rust/compiler/src/hir/lower/expr/helpers.rs`

**Final helper signature:**

```rust
/// Lower a positional argument list to `Vec<HirExpr>`.
///
/// **Drops `arg.name`** — this is intentional. All call sites using this helper
/// have already inspected `arg.name` upstream to dispatch struct-init vs positional
/// paths. Inside the lowering loop, names are never read.
///
/// TODO: if named-arg HIR ever lands (e.g., keyword arguments preserved into HirExpr),
/// call sites that use this helper must switch back to a name-aware loop.
pub(in crate::hir::lower) fn lower_call_args(
    &mut self,
    args: &[ast::Argument],
    ctx: &mut FunctionContext,
) -> LowerResult<Vec<HirExpr>> {
    let mut out = Vec::with_capacity(args.len());
    for arg in args {
        out.push(self.lower_expr(&arg.value, ctx)?);
    }
    Ok(out)
}
```

**Visibility:** `pub(in crate::hir::lower)` — matches the existing `lower_builtin_call` visibility in the same file.

**Migration steps:**
1. Add `lower_call_args` to `helpers.rs` (the `impl Lowerer` block already there).
2. Refactor `lower_builtin_call` (helpers.rs:12–26) to delegate: replace its inline loop with `let args_hir = self.lower_call_args(args, ctx)?;`.
3. Rewrite the 7 call sites to use `let args_hir = self.lower_call_args(args, ctx)?;` (or `let fields_hir = ...` at the struct-init sites — local name is fine):
   - `calls.rs:47–54` (enum ctor path)
   - `calls.rs:70–78` (struct-init from known type, `fields_hir`)
   - `calls.rs:89–97` (struct-init lenient, `fields_hir`)
   - `calls.rs:194–199` (generic lower_call fallthrough)
   - `mod.rs:272–275` (lower_builtin_method_call)
   - `mod.rs:386–389` (lower_method_call)
   - `simd.rs:240–244` (lower_static_method_call)
4. Run `cargo test` in the compiler crate — all existing HIR lowering tests must pass.
5. Commit: "refactor(hir/lower): extract lower_call_args helper from 7 inline loops".

**Behavioural-equivalence claim:** The helper is the exact 4-line loop that every site inlines. Error propagation via `?` is preserved in order. `Vec::with_capacity(args.len())` matches the implied allocation size. No span tracking is lost — `arg.value` carries its own span.

**Rollback plan:** Revert the single D1 commit. All 7 sites revert to their inline loops. `lower_builtin_call` reverts to its original body.

---

## 4. Perf Measurement Plan (C1)

C1 touches the hot Cranelift codegen path. Perf gate is mandatory before the C1+C2 commit lands.

**Baseline corpus:** Two representative files that the bootstrap chain actually compiles:
- `src/compiler/99.loader/module_loader.spl` (large, many method calls, exercises method codegen)
- `test/unit/compiler/loader/module_loader_spec.spl` (spec file, exercises call dispatch codegen)

**Tool:** `/usr/bin/time -v bin/simple build` (runs the full bootstrap chain — this is the codegen hot path, not `--mode=native` which false-greens per memory `feedback_compile_mode_false_greens`).

**Metric:** Wall-clock time (Elapsed wall clock time) and Maximum resident set size from `/usr/bin/time -v` output. Take the median of 3 runs warm (after one cold run to warm disk cache).

**Protocol:**
1. Record baseline on the commit immediately before C1: `for i in 1 2 3; do /usr/bin/time -v bin/simple build 2>&1 | grep -E 'wall clock|Maximum resident'; done`
2. Apply C1+C2 changes (do not commit yet).
3. Record post-change metrics with the same command.
4. Compute delta: if wall-clock regression ≥3% OR RSS regression ≥3% on the median run, the commit is blocked.

**Threshold:** ≥3% regression on either metric blocks the merge. This is a hard gate, not advisory.

**Mitigation:** If `#[inline]` on all helpers is insufficient and a regression appears:
- First try: annotate the two or three most-called helpers with `#[inline(always)]` instead of `#[inline]`.
- Fallback: convert the affected helpers to `macro_rules!` macros that expand inline. The macro approach eliminates all call overhead at the cost of slightly less readable error messages.

---

## 5. Test Scaffolding Shape

### A1 — Loader

**Spec file:** `test/unit/compiler/loader/module_loader_spec.spl` (already exists — augment, do not create new file).

**New test case to add:**
- Load a module via `loader.load(path)` (impl-method path, not free-function path).
- Call `loader.unload(path)` via the impl method (`loader.unload(path)`).
- Assert: `loader.modules` has no entry for path; `loader.global_symbols` has no entries from that module; `loader.jit.loaded_metadata` has no entry for path.
- Boundary cases: unload of never-loaded path (no-op, no panic); double unload (second call is no-op).
- Run in interpreter mode (per memory `feedback_compile_mode_false_greens`).

### B1 — SimpleOS Boot

**Two deliverables (both required):**

1. **Unit spec (fast feedback):** `test/unit/lib/nogc_async_mut/btreemap_spec.spl` — mirrors the existing `concurrent_providers_spec.spl` (which covers hashmap) but for btreemap/btreeset externs (`__rt_btreemap_new`, `__rt_btreemap_insert`, `__rt_btreemap_get`, `__rt_btreemap_remove`, `__rt_btreemap_len`). Run in interpreter mode.

2. **QEMU boot-path test:** `examples/simple_os/arch/x86_64/btreemap_test_entry.spl` — follows the pattern of `test_entry.spl`, `fs_test_entry.spl` etc. in the same directory. Must insert at least one btreemap entry, retrieve it, remove it, and assert empty — exercising the `IS_HEAP`/`DECODE_PTR` macros from the include path in `collections.c`. Run via `sh scripts/check-freebsd-bootstrap-qemu.shs --smoke` as the regression gate.

The QEMU test is mandatory for B1: the include replacement in `collections.c` and `hashmap.c` affects boot-path code that only runs in the QEMU environment, not in interpreter mode.

### C1 + C2 — Cranelift Instr Helpers

**Existing tests in `src/compiler_rust/compiler/tests/`:** `compile_and_run.rs`, `batch_pipeline.rs`, `native_link.rs`, `generic_template_tests.rs` exercise codegen paths. Run all of these as the regression gate.

**New test file:** `src/compiler_rust/compiler/tests/call_runtime_helpers.rs`
- Test `call_runtime_1` through `call_runtime_3` are reachable (exercise at least one codegen path per arity).
- Test `declare_uniform_i64_import` is idempotent (calling it twice with the same name does not panic or produce duplicate declarations).
- These can be integration tests using `compile_and_run` infrastructure already in the `common/` subdirectory.

### D1 — HIR Lower Expr

**Existing tests:** `src/compiler_rust/compiler/tests/bitfield_hir_lowering.rs`, `src/compiler_rust/compiler/tests/domain_block_hir_lowering.rs`. Run these as baseline.

**New test file:** `src/compiler_rust/compiler/tests/lower_call_args.rs`
- Test that positional calls, struct-init calls, method calls, and SIMD calls all lower correctly after the refactor.
- Specifically exercise: named-arg detection is still upstream of `lower_call_args` (i.e., the `args.iter().any(|a| a.name.is_some())` branch still fires correctly before the helper is called).
- Empty args list → `Ok(vec![])` (no panic).
- Single-error propagation: if `lower_expr` returns `Err`, `lower_call_args` propagates immediately (no partial results).

---

## 6. Risks the Implement Phase Must NOT Skip

1. **C1 perf measurement is mandatory.** Do not commit C1+C2 until wall-clock and RSS deltas are measured and within the 3% threshold. Use `bin/simple build` (bootstrap chain), not `--mode=native`. See Section 4.

2. **C1 `#[inline]` on every helper is mandatory.** Rust does not inline `pub(crate)` functions across module boundaries without `#[inline]`. Without it, the previous implicit inlining (from file-local private fns) is lost and a regression is near-certain. This is not advisory.

3. **C1 `unwrap_or_else(|| panic!(...))` is mandatory.** The existing `ctx.runtime_funcs[name]` index-operator panic produces a key-not-found message with no function context. The named panic message is required for debuggability parity. Do not leave the index operator form.

4. **B1 include order.** Each of the 4 consumer files must have `<stdint.h>` and `<stddef.h>` included before `baremetal_runtime.h`. The header's own docstring mandates this. Verified: all 4 files already have both system headers at the top. The include must go immediately after `<stddef.h>`, before any macro or type definition in the file.

5. **D1 `arg.name` drop comment is mandatory.** The `lower_call_args` docstring must include both:
   - The statement that `arg.name` is intentionally dropped.
   - The TODO: "if named-arg HIR ever lands, call sites using this helper must switch back to a name-aware loop."
   This must be a doc-comment (`///`) line, not an inline comment, so it appears in `cargo doc` output.

6. **No cover-up fixes (memory `feedback_no_coverups`).** If any existing test fails after a cluster's changes, the implement phase must fix the root cause. `skip()`, weakened assertions, and TODO→NOTE conversions are forbidden.

7. **One commit per cluster (AC-4).** C1+C2 ship together as one commit (same file, same owner). A1, B1, D1 each ship as separate commits. No bundled "chore: dedupe all" commits.

---

## 7. Estimated Total LOC Delta

| Cluster | Removed | Added | Net |
|---------|---------|-------|-----|
| A1 | −37 (38-line unload body → 1 line) | +1 | −37 |
| B1 | −78 (approx. 15+20+26+17 macro lines across 4 files) | +4 (#include lines) | −74 |
| C1 | −222 (74 open-coded sites × 3 lines avg) | +55 (5 helpers × ~11 lines each) | −167 |
| C2 | −48 (4 sites × 12 lines avg) | +18 (1 helper) | −30 |
| D1 | −28 (7 sites × 4 lines each) | +10 (1 helper + lower_builtin_call refactor) | −18 |
| **Total** | **−413** | **+88** | **−325** |

Estimates are based on visual inspection of call sites in research reports and source files. Actual delta may vary ±15% depending on exact blank-line conventions, but the net removal is solidly negative.
