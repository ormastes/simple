# Phase 3 (LLVM) Build Warning Report (2026-11-25)

## 1. Metadata & Evidence Source

- **Latest Phase 3 build artifact:** `C:\dev\p3diag\p3fix2_ll\build.log` (`2026-11-24 22:53 KST`, `85,077,180` bytes, `285,333` lines)
- **Summary record:** `C:\dev\p3diag\p3fix2_ll.summary` (`rc=0`, `secs=54779`, linked binary `27,537,408` bytes, `--version` sanity `rc=0`: `simple-bootstrap 1.0.0-rc.1`)
- **Build configuration:** LLVM backend, `24` MIR shard workers (`completed_workers=24`, `failed_workers=0`), `1,598` MIR modules (`57` native modules in final link)
- **Prior comparison log:** `C:\dev\p3diag\p4m_ll2\build.log` (`2026-11-23 08:45 KST`, `52,349,382` bytes, `710,762` lines, single-stream)
- **Freshness note:** No new Phase 3 full build has run since the `nil`/Option, bool-to-enum, `SPL-UNIT-002`, and Slang merges on `release/1.0.0`, which target separate lint categories and do not add or remove `E-MC-REP-001` or `E-MC-ANY-*` diagnostics.

---

## 2. Summary Counts (24-Worker Total vs Per-Worker vs Unique)

Because each of the **24 shard workers** executes HIR/MIR passes over the shared module set, almost every module-level diagnostic is emitted **24×** in the aggregated build log (`39,896` real diagnostic lines plus `48` pass-summary lines = `39,944` `[WARN]` / warning lines total). Deduplicating identical diagnostic lines yields **1,587 unique diagnostics** (**~1,670 diagnostics per worker**):

| Warning Category | Total Lines (24 workers) | Per-Worker | Unique (`p3fix2_ll`) | Prior Unique (`p4m_ll2`) | Description |
|---|---:|---:|---:|---:|---|
| `[WARN] [E-MC-REP-001]` | **26,328** | 1,097 | **1,038** | 1,650 | `unsafe` region missing owning representation reason and reviewers |
| `[WARN] [E-MC-ANY-002]` | **7,056** | 294 | **271** | 706 | Erased `Any` value escapes `type_erasure` boundary into container-typed binding |
| `[WARN] [E-MC-ANY-001]` | **6,432** | 268 | **268** | 420 | Binding declared `Any` in safe critical code (`294 + 268 = 562` per worker) |
| `[hir-lower] WARNING` | **8** | 8 | **8** | — | Bare unit enum variant over untyped subject (Catch-all risk) |
| `HIR lowering warning` (`[W-ANY-COMPILE-001]`) | **48** | 2 | **1** | 26 | `Any` in safe code (`join_point_attr_registry.spl`) |
| `[mir-lower] WARNING` | **24** | 1 | **1** | 31 | Struct `TextSpan` re-registered with differing field list |
| `[WARN] enum-contract pass` | 24 summaries | 0 diags | **0** | — | `enum-contract pass: 0 diagnostic(s)` |
| **Total real diagnostics** | **39,896** | **~1,670** | **1,587** | 2,833 | Plus 48 summary lines (`enum-contract pass` + `any-escape pass: 562 diagnostic(s)`) |

Note: between `p4m_ll2` (2026-11-23) and `p3fix2_ll` (2026-11-24), deduplicated warning counts dropped from **2,833** to **1,587** (**−44.0%**), and `enum-contract pass` reached **0** diagnostics.

---

## 3. Breakdown by Diagnostic Code

### 3.1 `E-MC-REP-001` — Unowned Representation in `unsafe` (1,038 unique)

Sample:
```text
app.cli.bootstrap_main: unsafe region in get_cli_args requires an owning representation reason and reviewers at 906:1
```

**By package prefix (`1,038` unique):**

| Prefix | Unique Diagnostics | Prefix | Unique Diagnostics |
|---|---:|---|---:|
| `lib.nogc_sync_mut` | 674 | `app.io` | 15 |
| `compiler.driver` | 81 | `compiler.types` | 10 |
| `lib.nogc_async_mut` | 75 | `compiler.mir_opt` | 6 |
| `compiler.backend` | 49 | `compiler.common` | 5 |
| `compiler.hir` | 32 | `compiler.interp` | 4 |
| `lib.common` | 31 | `app.cli` | 4 |
| `compiler.frontend` | 29 | `lib.scv` | 1 |
| `compiler.mir` | 22 | | |

**Top 10 modules:**
1. `lib.nogc_sync_mut.io.process_ops` — **103**
2. `lib.nogc_sync_mut.io_runtime` — **49**
3. `lib.nogc_sync_mut.simd` — **48**
4. `lib.nogc_sync_mut.sffi.fs` — **48**
5. `lib.nogc_sync_mut.atomic` — **28**
6. `lib.nogc_sync_mut.sffi.system` — **28**
7. `lib.nogc_sync_mut.sffi.io` — **27**
8. `lib.nogc_sync_mut.io.file_ops` — **26**
9. `compiler.driver.driver_entry_closure_core` — **22**
10. `lib.nogc_async_mut.io.platform_event` — **21**

---

### 3.2 `E-MC-ANY-001` — `Any` Binding in Safe Critical Code (268 unique)

Sample:
```text
app.cli.native_build_producer_binding: :bootstrap_native_build_producer_binding: `Any` is unavailable in safe critical code: this binding is declared `Any`; replace with a generic, a closed sum type, a typed interface, or an `unsafe(capabilities: [type_erasure])` boundary with checked conversion at 0:0
```

**By package prefix (`268` unique):**

| Prefix | Unique Diagnostics | Prefix | Unique Diagnostics |
|---|---:|---|---:|
| `lib.common` | 96 | `lib.scv` | 4 |
| `lib.nogc_sync_mut` | 84 | `app.build` | 4 |
| `compiler.frontend` | 32 | `compiler.loader` | 4 |
| `compiler.driver` | 18 | `compiler.hir` | 2 |
| `compiler.backend` | 17 | `compiler.common` | 1 |
| `app.cli` | 6 | | |

**Top 10 modules:**
1. `lib.nogc_sync_mut.compression.gzip.deflate` — **61**
2. `lib.common.serialization.__init__` — **56**
3. `lib.common.format_utils` — **23**
4. `compiler.frontend.core.interpreter.module_loader_core` — **16**
5. `lib.nogc_sync_mut.compression.gzip.lz77` — **15**
6. `lib.common.text_advanced` — **10**
7. `app.cli.native_build_producer_binding` — **6**
8. `compiler.frontend.core.alloc_inference` — **6**
9. `compiler.driver.smf.runtime_std_package_membership_v1` — **6**
10. `compiler.frontend.core.closure_analysis` — **6**

---

### 3.3 `E-MC-ANY-002` — Erased `Any` Escaping `type_erasure` Boundary (271 unique)

Sample:
```text
compiler.driver.driver_frozen_semantic_prerequisites_v1: :_diagnose_frozen_semantic_borrowed_v1: erased value escapes its type_erasure boundary: an erased value is stored in a container-typed binding; convert it to a concrete or closed-sum type before leaving the unsafe block at 0:0
```

**By package prefix (`271` unique):**

| Prefix | Unique Diagnostics | Prefix | Unique Diagnostics |
|---|---:|---|---:|
| `lib.nogc_sync_mut` | 62 | `compiler.loader` | 5 |
| `lib.common` | 57 | `compiler.mir` | 5 |
| `compiler.backend` | 49 | `compiler.hir` | 5 |
| `compiler.driver` | 38 | `lib.nogc_async_mut` | 4 |
| `compiler.frontend` | 12 | `compiler.semantics` | 4 |
| `app.build` | 8 | `compiler.interp` | 1 |
| `compiler.common` | 6 | `compiler.types` | 1 |
| `lib.scv` | 6 | `app.optimize` | 1 |
| `app.cli` | 6 | `compiler.mir_opt` | 1 |

**Top 10 modules:**
1. `lib.nogc_sync_mut.compression.gzip.deflate` — **48**
2. `lib.common.serialization.__init__` — **32**
3. `lib.common.format_utils` — **10**
4. `compiler.driver.smf.runtime_std_native_sections_v1` — **7**
5. `compiler.driver.smf.runtime_std_package_membership_v1` — **7**
6. `lib.scv.structural_store_v1` — **6**
7. `lib.common.text_advanced` — **6**
8. `compiler.loader.jit_instantiator` — **5**
9. `compiler.backend.linker._SmfReaderMemory.header_parser` — **5**
10. `app.cli.native_build_producer_binding` — **5**

---

### 3.4 Exact Single-Site Diagnostics (`[hir-lower]`, `W-ANY-COMPILE-001`, `[mir-lower]`)

**8 `[hir-lower] WARNING` sites (bare unit variant over untyped subject):**

| File | Bare Variant(s) |
|---|---|
| `src/compiler/80.driver/driver_unit_tldr_imports_v1.spl` | `None` |
| `src/compiler/85.mdsoc/weaving/weaving_config.spl` | `Before`, `AfterSuccess`, `AfterError`, `Around` |
| `src/compiler/30.types/type_infer/inference_expr.spl` | `Bool`, `Char` |
| `src/compiler/30.types/type_infer/inference_expr_ops.spl` | `Str` |

**1 `W-ANY-COMPILE-001` site (`HIR lowering warning`):**
- `src/compiler/10.frontend/join_point_attr_registry.spl`: `Any` is not allowed in safe code; use `<T>`, a concrete type, or `unsafe(capabilities: [type_erasure])`.

**1 `[mir-lower] WARNING` site:**
- Struct `TextSpan` re-registered with differing field list (`existing=[start, end]` vs `new=[value, start, len]`).

---

## 4. Recommended Burn-Down Order

1. **Zero-effort quick wins (10 unique warnings across 6 files):**
   - Qualify or type the subjects for the **8** `[hir-lower] WARNING` sites (`driver_unit_tldr_imports_v1.spl`, `weaving_config.spl`, `inference_expr.spl`, `inference_expr_ops.spl`).
   - Fix the **1** `W-ANY-COMPILE-001` in `join_point_attr_registry.spl` and rename/align the duplicate `TextSpan` definition (`[mir-lower] WARNING`).
2. **Highest-leverage `E-MC-ANY-001` + `E-MC-ANY-002` (~37% of all 539 `Any` diagnostics in 2 files):**
   - Replace `Any` in `lib.nogc_sync_mut.compression.gzip.deflate` (**61** `ANY-001` + **48** `ANY-002` = `109`) and `lib.common.serialization.__init__` (**56** `ANY-001` + **32** `ANY-002` = `88`), then `lib.common.format_utils` (`33`).
3. **Highest-leverage `E-MC-REP-001` (~65% of all 1,038 representation warnings):**
   - Add owning representation reason + reviewers to `unsafe` regions in `lib.nogc_sync_mut` (**674** unique, led by `io.process_ops` 103, `io_runtime` 49, `simd` 48, `sffi.fs` 48), followed by `compiler.driver` (81) and `lib.nogc_async_mut` (75).
4. **Related type-hardening tracking:** `doc/08_tracking/todo/type_hardening_nil_remaining_2026-11-25.md`.
