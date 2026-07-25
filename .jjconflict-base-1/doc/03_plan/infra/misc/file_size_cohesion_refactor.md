# File Size & Cohesion Refactor — Status

Status: LINE-COUNT TARGET MET — broad suite has unrelated existing failures.

Fresh line-count evidence shows zero real `src/**/*.spl` files over 800 lines:

```bash
while IFS= read -r -d '' f; do [ -f "$f" ] || continue; n=$(wc -l < "$f") || continue; if [ "$n" -gt 800 ]; then printf '%s %s\n' "$n" "$f"; fi; done < <(find src -name '*.spl' -print0) | sort -nr
# no output
```

This plan now records the original remaining-work inventory for traceability. Oversized files have since been split into small re-export aggregators plus sibling part modules.

## Approach
- 4 parallel Sonnet agents per wave, grouped by disjoint directories
- For large `class` + `impl` blocks: extract methods as free functions (no cross-file impl outside src/lib/)
- `bin/simple build lint` after each wave, `jj commit` + push after lint passes

## src/os/ — 19 files

| Lines | File |
|------:|------|
| 3038 | `os/qemu_runner.spl` |
| 1896 | `os/apps/shell/shell_app.spl` |
| 1741 | `os/tls13/tls13.spl` |
| 1175 | `os/drivers/virtio/virtio_blk.spl` |
| 1116 | `os/port/simpleos_multiplatform_build.spl` |
| 1071 | `os/services/llm/mcp_os_server.spl` |
| 1057 | `os/tls13/cert_verify.spl` |
| 1014 | `os/services/netstack/tcp_connection.spl` |
| 970 | `os/port/bootstrap_cross.spl` |
| 959 | `os/kernel/scheduler/scheduler.spl` |
| 930 | `os/apps/file_explorer/file_explorer.spl` |
| 927 | `os/services/netstack/netstack_service.spl` |
| 893 | `os/apps/shell/shell_tools.spl` |
| 856 | `os/userlib/window.spl` |
| 830 | `os/tools/net/ssh_tool.spl` |
| 803 | `os/drivers/nvme/nvme_driver.spl` |
| 801 | `os/drivers/virtio/virtio_net.spl` |

## src/app/ — 12 files

| Lines | File |
|------:|------|
| 1588 | `app/svim/core.spl` |
| 1476 | `app/traceability/core.spl` |
| 1371 | `app/wm_compare/html_compat.spl` |
| 1189 | `app/mcp/assistant/session_store.spl` |
| 1130 | `app/wm_compare/main.spl` |
| 1108 | `app/io/cli_commands.spl` |
| 1095 | `app/io/cli_compile.spl` |
| 989 | `app/cli/query_visibility.spl` |
| 982 | `app/cli/main.spl` |
| 897 | `app/cli_debug/commands.spl` |
| 854 | `app/ui.web/taskbar_runtime.spl` |
| 850 | `app/ui.render/tui_widgets.spl` |

## src/compiler/ — 24 files

| Lines | File |
|------:|------|
| 1538 | `compiler/90.tools/lint/main.spl` |
| 1390 | `compiler/30.types/type_layout.spl` |
| 1390 | `compiler/10.frontend/core/parser_decls.spl` |
| 1359 | `compiler/35.semantics/lint/simd_opportunity_lint.spl` |
| 1298 | `compiler/20.hir/hir_lowering/items.spl` |
| 1291 | `compiler/50.mir/mir_lowering_expr.spl` |
| 1288 | `compiler/70.backend/backend/native/x86_64_avx512.spl` |
| 1158 | `compiler/70.backend/backend/c_backend_translate.spl` |
| 1150 | `compiler/00.common/attributes.spl` |
| 1137 | `compiler/10.frontend/core/interpreter/eval_ops.spl` |
| 1078 | `compiler/70.backend/backend/mir_to_llvm.spl` |
| 1068 | `compiler/10.frontend/core/ast.spl` |
| 1036 | `compiler/70.backend/backend/native/arm_neon.spl` |
| 1019 | `compiler/50.mir/mir_lowering.spl` |
| 997 | `compiler/10.frontend/core/parser_primary.spl` |
| 989 | `compiler/60.mir_opt/mir_opt/auto_vectorize.spl` |
| 980 | `compiler/10.frontend/flat_ast_bridge.spl` |
| 904 | `compiler/70.backend/linker/linker_wrapper.spl` |
| 843 | `compiler/70.backend/linker/elf_writer.spl` |
| 829 | `compiler/70.backend/linker/smf_reader_memory.spl` |
| 813 | `compiler/10.frontend/core/ast_expr.spl` |
| 809 | `compiler/30.types/type_system/stmt_check.spl` |
| 807 | `compiler/90.tools/duplicate_check/detector.spl` |
| 805 | `compiler/70.backend/backend/vhdl_process.spl` |

## src/compiler_rust/ + src/lib/ stragglers — 4 files

| Lines | File |
|------:|------|
| 935 | `lib/hardware/fpga_linux/soc_vhdl_gen.spl` |
| 842 | `compiler_rust/lib/std/src/verification/lean/codegen.spl` |
| 826 | `lib/nogc_sync_mut/tls/utilities.spl` |
| 803 | `compiler_rust/lib/std/src/tooling/deployment/optimization.spl` |

## Verification
```bash
find src/ -name "*.spl" -exec wc -l {} + | awk '$1 > 800 && $2 != "total"' | wc -l  # target: 0
bin/simple build lint
bin/simple build check
```

Observed verification:
- PASS: `bin/simple build lint` completed successfully; Rust clippy warnings remain in existing SIMD extern code.
- PASS: targeted checks completed for representative split modules: `src/os/apps/shell/shell_app.spl`, `src/compiler/50.mir/mir_lowering_expr.spl`, `src/compiler/35.semantics/lint/simd_opportunity_lint.spl`, and `src/os/qemu_runner.spl`.
- BLOCKED: `bin/simple build check` was started and stopped after proving broad unrelated failures in existing app, code-quality, DBFS, remote-JIT, baremetal, and usage/context-block suites. Do not treat those failures as evidence against the line-count split unless those suites are in scope.
