# Code Duplication Analysis Report

**Date:** 2026-03-14
**Tool:** jscpd 4.0.5 (token-based, Python tokenizer for `.spl`)
**Parameters:** `--min-lines 5 --min-tokens 30`
**Scope:** `src/` (excluding `*.smf`, `*_spec.spl`, `*_test.spl`)

---

## Overall Summary

| Region | Files | Lines | Clones | Dup Lines | Dup % |
|--------|-------|-------|--------|-----------|-------|
| **src/lib/** (stdlib) | 1,521 | 305,788 | 2,149 | ~42,200 | **13.80%** |
| src/lib/common/ | 712 | 145,351 | 1,220 | ~25,260 | 17.39% |
| src/lib/nogc_sync_mut/ | 635 | 125,284 | 733 | ~13,720 | 10.95% |
| src/lib/nogc_async_mut/ | 151 | 30,206 | 182 | ~2,885 | 9.55% |
| src/lib/gc_async_mut/ | 23 | 4,947 | 14 | ~326 | 6.59% |
| **src/compiler/** | ~580 | ~195,000 | ~770 | ~8,600 | ~4.40% |
| src/compiler/70.backend | 202 | 52,441 | 293 | 2,854 | 5.44% |
| src/compiler/15.blocks | — | 4,403 | 31 | 262 | 5.95% |
| src/compiler/10.frontend | — | 33,431 | 187 | 1,649 | 4.93% |
| src/compiler/30.types | 55 | 18,910 | 99 | 817 | 4.32% |
| src/compiler/80.driver | — | — | 89 | — | 4.41% |
| src/compiler/50.mir | 17 | 4,643 | 23 | 206 | 4.44% |
| src/compiler/60.mir_opt | 23 | 7,171 | 39 | 290 | 4.04% |
| src/compiler/55.borrow | 10 | 2,831 | 10 | 102 | 3.60% |
| src/compiler/99.loader | — | — | 23 | — | 3.43% |
| src/compiler/40.mono | 22 | 6,384 | 24 | 212 | 3.32% |
| src/compiler/35.semantics | 44 | 10,712 | 49 | 355 | 3.31% |
| src/compiler/95.interp | — | — | 7 | — | 3.10% |
| src/compiler/85.mdsoc | — | — | 9 | — | 1.86% |
| src/compiler/25.traits | 9 | 1,930 | 4 | 33 | 1.71% |
| src/compiler/00.common | — | 6,131 | 5 | 38 | 0.62% |
| **src/app/** | 241 | 44,831 | 240 | 2,347 | 5.24% |
| **Rust bootstrap** | ~1,594 | 450,746 | 1,670 | 68,385 | 15.17% |

---

## Top 10 Actionable Hotspots

### 1. lib/common/parser/ vs lib/common/pure/ (~980 lines)
Near-identical parser implementations. `parser_expr.spl` (452 lines) and `parser.spl` (446 lines) are structural clones.
**Action:** Extract shared parser core, parametrize differences.

### 2. lib/common/fault_detection.spl vs lib/common/sys/fault_detection.spl (164 lines, 100%)
Exact file copy.
**Action:** Delete one, re-export from the other.

### 3. lib/nogc_sync_mut/database/test_extended/database.spl (86.8% dup)
God object whose methods were split into sub-modules but the original was never cleaned up.
**Action:** Remove duplicated methods from the monolith, keep only the sub-module versions.

### 4. lib/nogc_sync_mut/dap/adapter/trace32.spl (66 cross-file clones)
Heavy duplication with other DAP adapters (gdb, lldb, etc.).
**Action:** Extract shared DAP adapter base trait/mixin.

### 5. compiler/70.backend/ RISC-V 32 vs 64 (308 lines identical)
`encode_riscv32` and `encode_riscv64` share 308 lines of identical encoding, plus `isel_riscv32` vs `isel_riscv64` (299 lines).
**Action:** Parametrize by word size, share encoding logic.

### 6. app/mcp/ + app/jupyter_kernel/ + app/lsp_mcp/ (JSON-RPC protocol cluster)
`main_lazy_json.spl` (84.2% dup), `jupyter_kernel/protocol.spl` (91.5% dup), `lsp_mcp/main.spl` (63%).
**Action:** Extract shared JSON-RPC/stdio protocol module.

### 7. app/tools/cat/wc/head/tail/tee/uniq/ (CLI boilerplate)
`tools/cat/main.spl` at 92.3% duplication. Shared argument parsing and file I/O patterns.
**Action:** Extract common CLI tool scaffold.

### 8. compiler/40.mono/deferred_deserialize.spl (41.14% internal dup)
Repeated deserialization boilerplate for struct/class/enum/trait. Also `metadata.spl` (18%) with 4 identical GenericXxxMeta constructors.
**Action:** Generate via template or extract shared deserialize helper.

### 9. compiler/10.frontend/alloc_inference.spl vs call_graph.spl (114 lines, 8 clones)
Identical graph traversal patterns.
**Action:** Extract shared graph visitor utility.

### 10. compiler/15.blocks/builtin_blocks_data vs builtin_blocks_shell (8+ cross-file clones)
Block registration boilerplate duplicated between data and shell block types.
**Action:** Extract shared registration template.

---

## Cleanest Regions

| Region | Dup % | Notes |
|--------|-------|-------|
| compiler/00.common | 0.62% | Exemplary — almost zero duplication |
| compiler/25.traits | 1.71% | Well-factored |
| compiler/85.mdsoc | 1.86% | Clean, only self-clones in config.spl |
| compiler/95.interp | 3.10% | 7 self-clones in MIR dispatch |

---

## Per-Region Patterns

### Stdlib (src/lib/) — 13.80% overall

- **common/**: Parser duplication dominates. Also fault_detection exact copy, text processing utilities with overlapping implementations.
- **nogc_sync_mut/**: DAP adapter cluster (trace32/gdb/lldb share protocol handling), database God object, test_runner shared patterns.
- **nogc_async_mut/**: MCP server implementations share JSON handling. 9.55% — moderate.
- **gc_async_mut/**: Cleanest stdlib module at 6.59%.

### Compiler (src/compiler/) — ~4.40% overall

- **70.backend**: Architecture-specific code is the main driver. RISC-V 32/64, AArch64/x86_64, ELF/Mach-O pairs.
- **30.types**: Type layout match arms repeated. Inference expressions share patterns across bidirectional/phase files.
- **10.frontend**: Parser expressions and statements share token handling. alloc_inference ↔ call_graph graph traversal.
- **60.mir_opt**: Optimization passes share MIR traversal/transform scaffolding.
- **40.mono**: Type-based repetition — identical code for Function/Struct/Class/Enum/Trait metadata.

### Applications (src/app/) — 5.24%

- **Protocol cluster**: MCP, Jupyter, LSP-MCP share JSON-RPC/stdio code.
- **CLI query cluster**: query_engine, query_sem_query, query_helpers share dispatch logic.
- **CLI tools**: cat/wc/head/tail/tee/uniq share argument parsing.

### Rust Bootstrap (src/compiler_rust/) — 15.17%

- **loader/ vs runtime/src/loader/**: Near-complete crate duplication (~10,140 lines).
- **mock_helper vs simple_mock_helper**: Full directory copy (~4,204 lines).
- Largest single clone: 721 lines (fluent.rs).

---

## Methodology Notes

- **Tool:** jscpd 4.0.5 with `--formats-exts "python:spl"` (uses Python tokenizer for `.spl` files)
- **Token-based:** Detects structural similarity regardless of identifier names
- **Limitations:** Python tokenizer may miss Simple-specific syntax; exact cosine similarity not available (jscpd uses token hash matching)
- **Native tool blocked:** `bin/simple duplicate-check` is broken due to INTERP-DICT-001 (dict type annotation bug in interpreter mode)
