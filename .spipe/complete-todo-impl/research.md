# Research Report: pass_todo Stub Import Analysis

## Summary

- **Total stubs:** 237
- **HIGH priority** (imported by real non-stub code): **149**
- **LOW priority** (imported only by other stubs): **0**
- **SKIP** (not imported anywhere): **88**

*Note: No stubs were found that are imported only by other stubs (all importers were real code or none).*

## Top Priority Stubs by Import Count

| Import Count | Module | Expected Symbols |
|---:|---|---|
| 321 | `std.common` | target., units.model.world_units., hash_utils., types., json.parser. |
| 59 | `std.common.engine.ids` | (module-level) |
| 50 | `std.common.engine.math2d` | (module-level) |
| 41 | `std.common.engine.units` | (module-level) |
| 34 | `std.common.engine.math3d` | (module-level) |
| 33 | `std.common.engine.color` | (module-level) |
| 33 | `std.js.types.js_types` | JsValue, JsObject, JsProperty |
| 31 | `std.crypto` | hmac., types., sha256., sha512., legacy_hash. |
| 27 | `std.js.types.pair` | (module-level) |
| 21 | `std.common.engine.rect` | (module-level) |
| 20 | `std.js.types.ast_types` | JsExpression, JsStatement, SwitchCase |
| 16 | `std.crypto.types` | (module-level) |
| 14 | `std.common.drawing.vector` | (module-level) |
| 13 | `std.crypto.hmac` | (module-level) |
| 13 | `std.gc_async_mut.debug.remote.types` | (module-level) |
| 9 | `std.exp` | config, storage, run, artifact, query |
| 7 | `app.office.sheets.cell` | (module-level) |
| 7 | `std.common.torch.dyn_sffi_ops` | (module-level) |
| 7 | `std.gc_async_mut.gpu.browser_engine.simple_web_renderer` | (module-level) |
| 7 | `std.nogc_sync_mut.http_client` | types. |
| 6 | `app.office.planner.task` | (module-level) |
| 6 | `app.office.slides.slide` | (module-level) |
| 6 | `app.package.registry.config` | (module-level) |
| 6 | `app.package.registry.types` | (module-level) |
| 6 | `std.common.compress.types` | (module-level) |
| 6 | `std.common.torch.dyn_sffi_tensor_ops` | (module-level) |
| 6 | `std.crypto.sha256` | (module-level) |
| 6 | `std.crypto.sha512` | (module-level) |
| 6 | `std.editor.view.diagnostics_panel` | (module-level) |
| 6 | `std.editor.view.wiki_panel` | (module-level) |

## HIGH Priority Stubs (Imported by Real Code)

Format: module path → file, consumers, expected symbols

### app.build.build_cli

**`app.build.build_cli`**
- File: `src/app/build/build_cli.spl`
- Imported by 2 file(s):
  - `src/app/io/cli_compile_part1.spl`
  - `src/app/io/cli_compile_part2.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.build.cli_entry

**`app.build.cli_entry`**
- File: `src/app/build/cli_entry.spl`
- Imported by 1 file(s):
  - `src/app/cli/main_part1.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.build.render_adapter

**`app.build.render_adapter`**
- File: `src/app/build/render_adapter.spl`
- Imported by 1 file(s):
  - `src/app/ui.render/core.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.debug.debug_info_bridge

**`app.debug.debug_info_bridge`**
- File: `src/app/debug/debug_info_bridge.spl`
- Imported by 3 file(s):
  - `src/app/debug/remote/feature/register_gdb.spl`
  - `src/lib/nogc_sync_mut/debug/remote/feature/register_gdb.spl`
  - `src/lib/nogc_async_mut/debug/remote/feature/register_gdb.spl`
- Expected symbols: `DebugInfoBridge`

### app.debug.formats

**`app.debug.formats.dwarf_parser`**
- File: `src/app/debug/formats/dwarf_parser.spl`
- Imported by 3 file(s):
  - `src/app/debug/remote/feature/register_gdb.spl`
  - `src/lib/nogc_sync_mut/debug/remote/feature/register_gdb.spl`
  - `src/lib/nogc_async_mut/debug/remote/feature/register_gdb.spl`
- Expected symbols: `DwarfParser`

### app.debug.remote

**`app.debug.remote.backend_generic`**
- File: `src/app/debug/remote/backend_generic.spl`
- Imported by 5 file(s):
  - `src/app/debug/remote/backend.spl`
  - `src/lib/nogc_sync_mut/debug/remote/backend.spl`
  - `src/lib/nogc_sync_mut/debug/remote/backend_arm.spl`
  - `src/lib/nogc_async_mut/debug/remote/backend.spl`
  - `src/lib/nogc_async_mut/debug/remote/backend_arm.spl`
- Expected symbols: `RemoteGenericBackend`

### app.office.launcher

**`app.office.launcher`**
- File: `src/app/office/launcher.spl`
- Imported by 1 file(s):
  - `src/app/osffice/mod.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.mail

**`app.office.mail.compose`**
- File: `src/app/office/mail/compose.spl`
- Imported by 1 file(s):
  - `src/app/osffice/mail/mail_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.mail.folders`**
- File: `src/app/office/mail/folders.spl`
- Imported by 1 file(s):
  - `src/app/osffice/mail/mail_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.mail.mail_app`**
- File: `src/app/office/mail/mail_app.spl`
- Imported by 2 file(s):
  - `src/app/osffice/mod.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.mail.message`**
- File: `src/app/office/mail/message.spl`
- Imported by 5 file(s):
  - `src/app/osffice/mail/compose.spl`
  - `src/app/osffice/mail/folders.spl`
  - `src/app/osffice/mail/protocol.spl`
  - `src/app/osffice/mail/mail_app.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.planner

**`app.office.planner.board`**
- File: `src/app/office/planner/board.spl`
- Imported by 5 file(s):
  - `src/app/osffice/planner/list_view.spl`
  - `src/app/osffice/planner/calendar_view.spl`
  - `src/app/osffice/planner/kanban.spl`
  - `src/app/osffice/planner/planner_app.spl`
  - `src/app/osffice/planner/timeline.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.calendar_view`**
- File: `src/app/office/planner/calendar_view.spl`
- Imported by 1 file(s):
  - `src/app/osffice/planner/planner_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.kanban`**
- File: `src/app/office/planner/kanban.spl`
- Imported by 1 file(s):
  - `src/app/osffice/planner/planner_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.list_view`**
- File: `src/app/office/planner/list_view.spl`
- Imported by 1 file(s):
  - `src/app/osffice/planner/planner_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.planner_app`**
- File: `src/app/office/planner/planner_app.spl`
- Imported by 2 file(s):
  - `src/app/osffice/mod.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.task`**
- File: `src/app/office/planner/task.spl`
- Imported by 6 file(s):
  - `src/app/osffice/planner/board.spl`
  - `src/app/osffice/planner/list_view.spl`
  - `src/app/osffice/planner/calendar_view.spl`
  - `src/app/osffice/planner/kanban.spl`
  - `src/app/osffice/planner/planner_app.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.planner.timeline`**
- File: `src/app/office/planner/timeline.spl`
- Imported by 1 file(s):
  - `src/app/osffice/planner/planner_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.render_adapter

**`app.office.render_adapter`**
- File: `src/app/office/render_adapter.spl`
- Imported by 3 file(s):
  - `src/app/ui.render/core.spl`
  - `src/app/ui/cli_entry.spl`
  - `src/app/osffice/mod.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.sheets

**`app.office.sheets.cell`**
- File: `src/app/office/sheets/cell.spl`
- Imported by 7 file(s):
  - `src/app/osffice/sheets/cell_ref.spl`
  - `src/app/osffice/sheets/csv_io.spl`
  - `src/app/osffice/sheets/formula.spl`
  - `src/app/osffice/sheets/sheets_app.spl`
  - `src/app/osffice/sheets/spreadsheet.spl`
  - ... and 2 more
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.sheets.cell_ref`**
- File: `src/app/office/sheets/cell_ref.spl`
- Imported by 1 file(s):
  - `src/app/osffice/sheets/formula.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.sheets.formula`**
- File: `src/app/office/sheets/formula.spl`
- Imported by 1 file(s):
  - `src/app/osffice/sheets/sheets_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.sheets.sheets_app`**
- File: `src/app/office/sheets/sheets_app.spl`
- Imported by 2 file(s):
  - `src/app/osffice/mod.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.sheets.spreadsheet`**
- File: `src/app/office/sheets/spreadsheet.spl`
- Imported by 3 file(s):
  - `src/app/osffice/sheets/csv_io.spl`
  - `src/app/osffice/sheets/formula.spl`
  - `src/app/osffice/sheets/sheets_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.slides

**`app.office.slides.render`**
- File: `src/app/office/slides/render.spl`
- Imported by 3 file(s):
  - `src/app/osffice/slides/presenter.spl`
  - `src/app/osffice/slides/slides_app.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.slides.slide`**
- File: `src/app/office/slides/slide.spl`
- Imported by 6 file(s):
  - `src/app/osffice/slides/presenter.spl`
  - `src/app/osffice/slides/render.spl`
  - `src/app/osffice/slides/templates.spl`
  - `src/app/osffice/slides/slides_app.spl`
  - `src/app/osffice/mod.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.slides.slides_app`**
- File: `src/app/office/slides/slides_app.spl`
- Imported by 2 file(s):
  - `src/app/osffice/mod.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.slides.templates`**
- File: `src/app/office/slides/templates.spl`
- Imported by 1 file(s):
  - `src/app/osffice/slides/slides_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.theme

**`app.office.theme`**
- File: `src/app/office/theme.spl`
- Imported by 1 file(s):
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.office.word

**`app.office.word.render`**
- File: `src/app/office/word/render.spl`
- Imported by 2 file(s):
  - `src/app/osffice/word/word_app.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.word.sidebar`**
- File: `src/app/office/word/sidebar.spl`
- Imported by 1 file(s):
  - `src/app/osffice/word/word_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.word.toolbar`**
- File: `src/app/office/word/toolbar.spl`
- Imported by 1 file(s):
  - `src/app/osffice/word/word_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.office.word.word_app`**
- File: `src/app/office/word/word_app.spl`
- Imported by 2 file(s):
  - `src/app/osffice/mod.spl`
  - `src/app/osffice/render_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.package.registry

**`app.package.registry.auth`**
- File: `src/app/package/registry/auth.spl`
- Imported by 3 file(s):
  - `src/app/publish/main.spl`
  - `src/app/yank/main.spl`
  - `src/app/package.registry/oci.spl`
- Imported as whole module (no specific symbols extracted from use line)

**`app.package.registry.config`**
- File: `src/app/package/registry/config.spl`
- Imported by 6 file(s):
  - `src/app/info/main.spl`
  - `src/app/publish/main.spl`
  - `src/app/search/main.spl`
  - `src/app/yank/main.spl`
  - `src/app/package.registry/auth.spl`
  - ... and 1 more
- Imported as whole module (no specific symbols extracted from use line)

**`app.package.registry.index`**
- File: `src/app/package/registry/index.spl`
- Imported by 3 file(s):
  - `src/app/info/main.spl`
  - `src/app/search/main.spl`
  - `src/app/yank/main.spl`
- Imported as whole module (no specific symbols extracted from use line)

**`app.package.registry.oci`**
- File: `src/app/package/registry/oci.spl`
- Imported by 1 file(s):
  - `src/app/publish/main.spl`
- Imported as whole module (no specific symbols extracted from use line)

**`app.package.registry.signing`**
- File: `src/app/package/registry/signing.spl`
- Imported by 1 file(s):
  - `src/app/package.registry/verify.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.package.registry.trust`**
- File: `src/app/package/registry/trust.spl`
- Imported by 1 file(s):
  - `src/app/package.registry/verify.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`app.package.registry.types`**
- File: `src/app/package/registry/types.spl`
- Imported by 6 file(s):
  - `src/app/info/main.spl`
  - `src/app/publish/main.spl`
  - `src/app/package.registry/auth.spl`
  - `src/app/package.registry/config.spl`
  - `src/app/package.registry/index.spl`
  - ... and 1 more
- Imported as whole module (no specific symbols extracted from use line)

### app.test_cache_shared

**`app.test_cache_shared`**
- File: `src/app/test_cache_shared.spl`
- Imported by 5 file(s):
  - `src/app/test_runner_new/test_runner_files.spl`
  - `src/app/test_runner_new/test_result_cache.spl`
  - `src/app/test_daemon/cache.spl`
  - `src/app/test_incremental_state_shared.spl`
  - `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.test_runner_new.test_db_migrate

**`app.test_runner_new.test_db_migrate`**
- File: `src/app/test_runner_new/test_db_migrate.spl`
- Imported by 1 file(s):
  - `src/app/cli/test_db_repair.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.test_runner_new.test_db_perf

**`app.test_runner_new.test_db_perf`**
- File: `src/app/test_runner_new/test_db_perf.spl`
- Imported by 1 file(s):
  - `src/app/cli/test_db_repair.spl`
- Symbols: (inline/qualified usage — check consumer files)

### app.ui.cli

**`app.ui.cli`**
- File: `src/app/ui/cli.spl`
- Imported by 2 file(s):
  - `src/app/ui.cli/__init__.spl`
  - `src/app/ui/main.spl`
- Expected symbols: `observer.`

### compiler.core.hir

**`compiler.core.hir.lowering`**
- File: `src/compiler/core/hir/lowering.spl`
- Imported by 1 file(s):
  - `src/compiler/10.frontend/core/hir/test_hir_lower.spl`
- Symbols: (inline/qualified usage — check consumer files)

### compiler.core.mir

**`compiler.core.mir.lowering`**
- File: `src/compiler/core/mir/lowering.spl`
- Imported by 1 file(s):
  - `src/compiler/10.frontend/core/mir/test_mir_lower.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.cc.entity

**`std.cc.entity.property_tree`**
- File: `src/lib/cc/entity/property_tree.spl`
- Imported by 1 file(s):
  - `src/lib/viz/feature/aggregator_compose.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common

**`std.common`**
- File: `src/lib/common.spl`
- Imported by 321 file(s):
  - `src/compiler/70.backend/backend/arm_asm.spl`
  - `src/compiler/70.backend/backend/riscv_asm.spl`
  - `src/compiler/70.backend/backend/x86_asm.spl`
  - `src/compiler/70.backend/inline_asm.spl`
  - `src/compiler/30.types/units/unit_registry.spl`
  - ... and 316 more
- Expected symbols: `target.`, `units.model.world_units.`, `hash_utils.`, `types.`, `json.parser.`, `json.serializer.`, `json.types.`, `json.object_ops.`, `json.array_ops.`, `base_encoding.`, `text_advanced.`, `json.path_ops.`, `json.`, `encoding.base64.`, `report.ansi.`, `base_encoding.base64.`, `base_encoding.utilities.`, `crypto.types.`, `bcrypt.hash.`, `bcrypt.verify.`, `web.node_types.`, `web.attribute_types.`, `render_scene.css_types.`, `web.event_types.`, `render_scene.box_types.`, `render_scene.paint_types.`, `color.types.`, `color.convert.`, `image.ppm_decode.`, `markdown`, `compress.types.`, `compress.deflate.`, `io.traits.`, `io.types.`, `gpu.device.`, `torch.interface.`, `torch.dyn_sffi.`, `torch.dyn_sffi_ops.`, `torch.dyn_sffi_tensor_ops.`, `engine.rect.`, `engine.color.`, `engine.units.`, `engine.math3d.`, `engine.math2d.`, `engine.ids.`, `math.`, `engine.signal.signal.`, `aes.modes.`, `aes.utilities.`, `bcrypt.key_derivation.`, `jwt.decode.`, `jwt.claims.`, `bcrypt.salt.`, `web.dom.`, `web.event.`, `drawing.document.`, `drawing.vector.`, `drawing.selection.`, `command.history.`, `editor.scene_format.`, `sdn.value.`, `sdn.parser.`, `science_math.lapack_provider.`, `science_math.lapack.`, `science_math.blas_provider.`, `science_math.fortran_abi.`, `jwt.verify.`, `crypto.sha256.`, `io.async_traits.`, `validation.`, `crypto.hmac.`, `science_math.ndarray.`, `science_math.math_block.`, `compress.utilities.`, `compress.zstd.`, `compress.lz4.`, `text.`, `compress.gzip.`, `cbor.encode.`, `cbor.decode.`, `math.field.fe_p256.`

### std.common.base_encoding

**`std.common.base_encoding`**
- File: `src/lib/common/base_encoding.spl`
- Imported by 3 file(s):
  - `src/app/release/github.spl`
  - `src/app/itf/adapter_jira_curl.spl`
  - `src/lib/nogc_sync_mut/terminal/credential/store.spl`
- Expected symbols: `base64.`, `utilities.`

### std.common.command

**`std.common.command.history`**
- File: `src/lib/common/command/history.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/drawing/tool_app.spl`
  - `src/lib/nogc_sync_mut/editor/app.spl`
  - `src/lib/nogc_async_mut/drawing/tool_app.spl`
  - `src/lib/nogc_async_mut/editor/app.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.compress

**`std.common.compress.deflate`**
- File: `src/lib/common/compress/deflate.spl`
- Imported by 3 file(s):
  - `src/lib/nogc_sync_mut/http/ws/permessage_deflate.spl`
  - `src/lib/gc_async_mut/http/ws/permessage_deflate.spl`
  - `src/lib/nogc_async_mut/http/ws/permessage_deflate.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.compress.lz4`**
- File: `src/lib/common/compress/lz4.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_async_mut/http_server/compression.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.compress.types`**
- File: `src/lib/common/compress/types.spl`
- Imported by 6 file(s):
  - `src/lib/nogc_sync_mut/compression/brotli/bit_reader.spl`
  - `src/lib/nogc_sync_mut/compression/brotli/decoder.spl`
  - `src/lib/nogc_sync_mut/compression/brotli/decoder_block.spl`
  - `src/lib/nogc_sync_mut/compression/brotli/decoder_huffman.spl`
  - `src/lib/nogc_sync_mut/compression/brotli/decoder_tables.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.compress.utilities`**
- File: `src/lib/common/compress/utilities.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_async_mut/http_server/compression.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.compress.zstd`**
- File: `src/lib/common/compress/zstd.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_async_mut/http_server/compression.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.crypto

**`std.common.crypto.hmac`**
- File: `src/lib/common/crypto/hmac.spl`
- Imported by 2 file(s):
  - `src/lib/nogc_sync_mut/aws_sigv4.spl`
  - `src/lib/nogc_async_mut/aws_sigv4.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.crypto.sha256`**
- File: `src/lib/common/crypto/sha256.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/security/audit_chain.spl`
  - `src/lib/nogc_sync_mut/aws_sigv4.spl`
  - `src/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack.spl`
  - `src/lib/nogc_async_mut/aws_sigv4.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.crypto.types`**
- File: `src/lib/common/crypto/types.spl`
- Imported by 2 file(s):
  - `src/app/itf/adapter_minio.spl`
  - `src/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.drawing

**`std.common.drawing.document`**
- File: `src/lib/common/drawing/document.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/drawing/compositor.spl`
  - `src/lib/nogc_sync_mut/drawing/tool_app.spl`
  - `src/lib/nogc_async_mut/drawing/compositor.spl`
  - `src/lib/nogc_async_mut/drawing/tool_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.drawing.selection`**
- File: `src/lib/common/drawing/selection.spl`
- Imported by 2 file(s):
  - `src/lib/nogc_sync_mut/drawing/tool_app.spl`
  - `src/lib/nogc_async_mut/drawing/tool_app.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.drawing.vector`**
- File: `src/lib/common/drawing/vector.spl`
- Imported by 14 file(s):
  - `src/lib/nogc_sync_mut/drawing/rasterizer.spl`
  - `src/lib/nogc_sync_mut/drawing/tool_app.spl`
  - `src/lib/nogc_sync_mut/editor/app.spl`
  - `src/lib/nogc_sync_mut/editor/gizmo.spl`
  - `src/lib/nogc_sync_mut/editor/panel.spl`
  - ... and 9 more
- Symbols: (inline/qualified usage — check consumer files)

### std.common.editor

**`std.common.editor.scene_format`**
- File: `src/lib/common/editor/scene_format.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/editor/panels/hierarchy.spl`
  - `src/lib/nogc_sync_mut/editor/panels/inspector.spl`
  - `src/lib/nogc_sync_mut/editor/app.spl`
  - `src/lib/nogc_async_mut/editor/app.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.engine

**`std.common.engine.color`**
- File: `src/lib/common/engine/color.spl`
- Imported by 33 file(s):
  - `src/lib/nogc_sync_mut/compositor/gpu_command.spl`
  - `src/lib/nogc_sync_mut/compositor/rasterizer.spl`
  - `src/lib/nogc_sync_mut/engine/component/particle.spl`
  - `src/lib/nogc_sync_mut/engine/component/sprite.spl`
  - `src/lib/nogc_sync_mut/engine/component/mesh.spl`
  - ... and 28 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.ids`**
- File: `src/lib/common/engine/ids.spl`
- Imported by 59 file(s):
  - `src/lib/nogc_sync_mut/engine/component/sprite.spl`
  - `src/lib/nogc_sync_mut/engine/component/tilemap.spl`
  - `src/lib/nogc_sync_mut/engine/component/registry.spl`
  - `src/lib/nogc_sync_mut/engine/component/registry3d.spl`
  - `src/lib/nogc_sync_mut/engine/core/engine3d.spl`
  - ... and 54 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.math2d`**
- File: `src/lib/common/engine/math2d.spl`
- Imported by 50 file(s):
  - `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl`
  - `src/lib/nogc_sync_mut/engine/audio/listener_system.spl`
  - `src/lib/nogc_sync_mut/engine/audio/occlusion.spl`
  - `src/lib/nogc_sync_mut/engine/component/camera.spl`
  - `src/lib/nogc_sync_mut/engine/component/particle.spl`
  - ... and 45 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.math3d`**
- File: `src/lib/common/engine/math3d.spl`
- Imported by 34 file(s):
  - `src/lib/nogc_sync_mut/engine/audio/types.spl`
  - `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl`
  - `src/lib/nogc_sync_mut/engine/audio/doppler.spl`
  - `src/lib/nogc_sync_mut/engine/audio/listener_system.spl`
  - `src/lib/nogc_sync_mut/engine/audio/occlusion.spl`
  - ... and 29 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.rect`**
- File: `src/lib/common/engine/rect.spl`
- Imported by 21 file(s):
  - `src/lib/nogc_sync_mut/compositor/damage.spl`
  - `src/lib/nogc_sync_mut/engine/component/camera.spl`
  - `src/lib/nogc_sync_mut/engine/component/particle.spl`
  - `src/lib/nogc_sync_mut/engine/component/sprite.spl`
  - `src/lib/nogc_sync_mut/engine/component/tilemap.spl`
  - ... and 16 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.signal.signal`**
- File: `src/lib/common/engine/signal/signal.spl`
- Imported by 5 file(s):
  - `src/lib/nogc_sync_mut/engine/input/input_manager.spl`
  - `src/lib/nogc_sync_mut/engine/physics/simple/world.spl`
  - `src/lib/nogc_sync_mut/engine/physics/simple/world3d.spl`
  - `src/lib/nogc_async_mut/engine/physics/simple/world.spl`
  - `src/lib/nogc_async_mut/engine/physics/simple/world3d.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.engine.units`**
- File: `src/lib/common/engine/units.spl`
- Imported by 41 file(s):
  - `src/lib/nogc_sync_mut/engine/audio/types.spl`
  - `src/lib/nogc_sync_mut/engine/audio/audio_group.spl`
  - `src/lib/nogc_sync_mut/engine/audio/audio_manager.spl`
  - `src/lib/nogc_sync_mut/engine/component/camera.spl`
  - `src/lib/nogc_sync_mut/engine/component/particle.spl`
  - ... and 36 more
- Symbols: (inline/qualified usage — check consumer files)

### std.common.image

**`std.common.image.ppm_decode`**
- File: `src/lib/common/image/ppm_decode.spl`
- Imported by 3 file(s):
  - `src/app/wm_compare/main_part1.spl`
  - `src/app/wm_compare/main_part2.spl`
  - `src/os/compositor/qemu_capture.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.jwt

**`std.common.jwt.claims`**
- File: `src/lib/common/jwt/claims.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/web_framework/auth_middleware.spl`
  - `src/lib/nogc_sync_mut/web_framework/password_reset.spl`
  - `src/lib/nogc_sync_mut/web_framework/rbac.spl`
  - `src/lib/nogc_sync_mut/oidc/id_token.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.jwt.decode`**
- File: `src/lib/common/jwt/decode.spl`
- Imported by 2 file(s):
  - `src/lib/nogc_sync_mut/web_framework/auth_middleware.spl`
  - `src/lib/nogc_sync_mut/oidc/id_token.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.jwt.verify`**
- File: `src/lib/common/jwt/verify.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_sync_mut/oidc/id_token.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.render_scene

**`std.common.render_scene.box_types`**
- File: `src/lib/common/render_scene/box_types.spl`
- Imported by 1 file(s):
  - `src/app/ui.browser/renderer.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.render_scene.css_types`**
- File: `src/lib/common/render_scene/css_types.spl`
- Imported by 2 file(s):
  - `src/app/ui.browser/dom_bridge.spl`
  - `src/app/ui.browser/renderer.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.render_scene.paint_types`**
- File: `src/lib/common/render_scene/paint_types.spl`
- Imported by 1 file(s):
  - `src/app/ui.browser/renderer.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.sdn

**`std.common.sdn.parser`**
- File: `src/lib/common/sdn/parser.spl`
- Imported by 3 file(s):
  - `src/lib/nogc_sync_mut/game2d/asset/loader.spl`
  - `src/lib/nogc_sync_mut/game2d/asset/table.spl`
  - `src/lib/nogc_sync_mut/game2d/config/game_sdn.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.sdn.value`**
- File: `src/lib/common/sdn/value.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/game2d/asset/diagnostic.spl`
  - `src/lib/nogc_sync_mut/game2d/asset/loader.spl`
  - `src/lib/nogc_sync_mut/game2d/asset/table.spl`
  - `src/lib/nogc_sync_mut/game2d/config/game_sdn.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.torch

**`std.common.torch.dyn_sffi`**
- File: `src/lib/common/torch/dyn_sffi.spl`
- Imported by 3 file(s):
  - `src/lib/nogc_sync_mut/torch/dyn_sffi.spl`
  - `src/lib/gc_async_mut/torch/dyn_sffi.spl`
  - `src/lib/nogc_async_mut/torch/dyn_sffi.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.torch.dyn_sffi_ops`**
- File: `src/lib/common/torch/dyn_sffi_ops.spl`
- Imported by 7 file(s):
  - `src/lib/nogc_sync_mut/torch/dyn_sffi.spl`
  - `src/lib/gc_async_mut/torch/dyn_sffi.spl`
  - `src/lib/nogc_async_mut/torch/dyn_sffi.spl`
  - `src/lib/nogc_async_mut/linalg/backend_ops.spl`
  - `src/lib/nogc_async_mut/linalg/linalg_core.spl`
  - ... and 2 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.torch.dyn_sffi_tensor_ops`**
- File: `src/lib/common/torch/dyn_sffi_tensor_ops.spl`
- Imported by 6 file(s):
  - `src/lib/nogc_sync_mut/torch/dyn_sffi.spl`
  - `src/lib/gc_async_mut/torch/dyn_sffi.spl`
  - `src/lib/nogc_async_mut/torch/dyn_sffi.spl`
  - `src/lib/nogc_async_mut/linalg/backend_ops.spl`
  - `src/lib/nogc_async_mut/linalg/torch_ndarray.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

### std.common.units

**`std.common.units.model.world_units`**
- File: `src/lib/common/units/model/world_units.spl`
- Imported by 1 file(s):
  - `src/compiler/30.types/units/unit_registry.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.common.web

**`std.common.web.attribute_types`**
- File: `src/lib/common/web/attribute_types.spl`
- Imported by 1 file(s):
  - `src/app/ui.browser/dom_bridge.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.web.dom`**
- File: `src/lib/common/web/dom.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.web.event`**
- File: `src/lib/common/web/event.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.web.event_types`**
- File: `src/lib/common/web/event_types.spl`
- Imported by 2 file(s):
  - `src/app/ui.browser/dom_bridge.spl`
  - `src/app/ui.chromium/event_bridge.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.common.web.node_types`**
- File: `src/lib/common/web/node_types.spl`
- Imported by 2 file(s):
  - `src/app/ui.browser/dom_bridge.spl`
  - `src/app/ui.browser/renderer.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.compute

**`std.compute`**
- File: `src/lib/compute.spl`
- Imported by 3 file(s):
  - `src/lib/nogc_sync_mut/src/testing/gpu_helpers.spl`
  - `src/lib/gc_async_mut/src/testing/gpu_helpers.spl`
  - `src/lib/nogc_async_mut/src/testing/gpu_helpers.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.content.entity

**`std.content.entity.web_contents`**
- File: `src/lib/content/entity/web_contents.spl`
- Imported by 1 file(s):
  - `src/lib/gui/entity/browser_window.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.content.feature

**`std.content.feature.render_widget_host_view`**
- File: `src/lib/content/feature/render_widget_host_view.spl`
- Imported by 1 file(s):
  - `src/lib/gui/entity/browser_window.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.crypto

**`std.crypto`**
- File: `src/lib/crypto.spl`
- Imported by 31 file(s):
  - `src/app/package.registry/signing.spl`
  - `src/app/package.registry/verify.spl`
  - `src/app/portal/services/auth_service.spl`
  - `src/app/web_stack_sample/app.spl`
  - `src/lib/nogc_sync_mut/http/auth/basic.spl`
  - ... and 26 more
- Expected symbols: `hmac.`, `types.`, `sha256.`, `sha512.`, `legacy_hash.`, `pbkdf2.`, `sha3.`, `sha1.`

### std.crypto.hmac

**`std.crypto.hmac`**
- File: `src/lib/crypto/hmac.spl`
- Imported by 13 file(s):
  - `src/app/portal/services/auth_service.spl`
  - `src/app/web_stack_sample/app.spl`
  - `src/lib/nogc_sync_mut/web_framework/auth_middleware.spl`
  - `src/lib/nogc_sync_mut/web_framework/csrf_integration.spl`
  - `src/lib/nogc_sync_mut/web_framework/password_reset.spl`
  - ... and 8 more
- Symbols: (inline/qualified usage — check consumer files)

### std.crypto.legacy_hash

**`std.crypto.legacy_hash`**
- File: `src/lib/crypto/legacy_hash.spl`
- Imported by 3 file(s):
  - `src/lib/nogc_sync_mut/http/auth/digest.spl`
  - `src/lib/gc_async_mut/http/auth/digest.spl`
  - `src/lib/nogc_async_mut/http/auth/digest.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.crypto.sha256

**`std.crypto.sha256`**
- File: `src/lib/crypto/sha256.spl`
- Imported by 6 file(s):
  - `src/lib/nogc_sync_mut/http/auth/digest.spl`
  - `src/lib/gc_async_mut/http/auth/digest.spl`
  - `src/lib/nogc_async_mut/http/auth/digest.spl`
  - `src/os/crypto/bip39.spl`
  - `src/os/crypto/scram_common.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

### std.crypto.sha512

**`std.crypto.sha512`**
- File: `src/lib/crypto/sha512.spl`
- Imported by 6 file(s):
  - `src/lib/nogc_sync_mut/http/auth/digest.spl`
  - `src/lib/gc_async_mut/http/auth/digest.spl`
  - `src/lib/nogc_async_mut/http/auth/digest.spl`
  - `src/os/crypto/ed25519.spl`
  - `src/os/crypto/scram_common.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

### std.crypto.types

**`std.crypto.types`**
- File: `src/lib/crypto/types.spl`
- Imported by 16 file(s):
  - `src/lib/nogc_sync_mut/http/auth/basic.spl`
  - `src/lib/nogc_sync_mut/http/auth/digest.spl`
  - `src/lib/nogc_sync_mut/http/auth/http_auth_spec.spl`
  - `src/lib/nogc_sync_mut/http/auth/.spipe_matchers_http_auth_spec.spl`
  - `src/lib/nogc_sync_mut/web_framework/password_reset.spl`
  - ... and 11 more
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.buffer

**`std.editor.buffer.buffer`**
- File: `src/lib/editor/buffer/buffer.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.buffer.piece_table`**
- File: `src/lib/editor/buffer/piece_table.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.buffer.undo`**
- File: `src/lib/editor/buffer/undo.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.core

**`std.editor.core.document`**
- File: `src/lib/editor/core/document.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.core.session`**
- File: `src/lib/editor/core/session.spl`
- Imported by 4 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
  - `src/app/editor/main.spl`
  - `src/app/svim/session_adapter.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.extensions

**`std.editor.extensions.api`**
- File: `src/lib/editor/extensions/api.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.builtin.md_commands`**
- File: `src/lib/editor/extensions/builtin/md_commands.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.builtin.md_edit_assist`**
- File: `src/lib/editor/extensions/builtin/md_edit_assist.spl`
- Imported by 3 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/editor_controller.spl`
  - `src/app/editor/tui_shell.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.builtin.md_language`**
- File: `src/lib/editor/extensions/builtin/md_language.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.builtin.md_vim_motions`**
- File: `src/lib/editor/extensions/builtin/md_vim_motions.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.builtin.spl_language`**
- File: `src/lib/editor/extensions/builtin/spl_language.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.extensions.manifest`**
- File: `src/lib/editor/extensions/manifest.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.render

**`std.editor.render.block_model`**
- File: `src/lib/editor/render/block_model.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.services

**`std.editor.services.command_palette`**
- File: `src/lib/editor/services/command_palette.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.editor.view

**`std.editor.view.diagnostics_panel`**
- File: `src/lib/editor/view/diagnostics_panel.spl`
- Imported by 6 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/editor_controller.spl`
  - `src/app/editor/gui_shell.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
  - `src/app/editor/tui_shell.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.dock_zone`**
- File: `src/lib/editor/view/dock_zone.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.file_tree`**
- File: `src/lib/editor/view/file_tree.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.layout`**
- File: `src/lib/editor/view/layout.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.lsp_result_panel`**
- File: `src/lib/editor/view/lsp_result_panel.spl`
- Imported by 5 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/editor_controller.spl`
  - `src/app/editor/gui_shell.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
  - `src/app/editor/tui_shell.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.outline_panel`**
- File: `src/lib/editor/view/outline_panel.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.settings_view`**
- File: `src/lib/editor/view/settings_view.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.split_tree`**
- File: `src/lib/editor/view/split_tree.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.tab`**
- File: `src/lib/editor/view/tab.spl`
- Imported by 2 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.editor.view.wiki_panel`**
- File: `src/lib/editor/view/wiki_panel.spl`
- Imported by 6 file(s):
  - `src/app/editor/debug_process_command_smoke.spl`
  - `src/app/editor/editor_controller.spl`
  - `src/app/editor/gui_shell.spl`
  - `src/app/editor/lsp_activate_smoke.spl`
  - `src/app/editor/tui_shell.spl`
  - ... and 1 more
- Symbols: (inline/qualified usage — check consumer files)

### std.encoding.simd_text_sffi

**`std.encoding.simd_text_sffi`**
- File: `src/lib/encoding/simd_text_sffi.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_sync_mut/benchmark/string_bench.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.exp

**`std.exp`**
- File: `src/lib/exp.spl`
- Imported by 9 file(s):
  - `src/app/exp/main.spl`
  - `src/lib/nogc_sync_mut/src/exp/artifact.spl`
  - `src/lib/nogc_sync_mut/src/exp/run.spl`
  - `src/lib/nogc_sync_mut/src/exp/sweep.spl`
  - `src/lib/nogc_sync_mut/src/exp/query.spl`
  - ... and 4 more
- Expected symbols: `config`, `storage`, `run`, `artifact`, `query`, `sweep`

### std.gc_async_mut.cuda

**`std.gc_async_mut.cuda`**
- File: `src/lib/gc_async_mut/cuda.spl`
- Imported by 3 file(s):
  - `src/lib/gc_async_mut/gpu/engine2d/cuda_session.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/render_2d_riscv.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.debug

**`std.gc_async_mut.debug.remote.exec.types`**
- File: `src/lib/gc_async_mut/debug/remote/exec/types.spl`
- Imported by 2 file(s):
  - `src/lib/gc_async_mut/jit/jit_layout.spl`
  - `src/lib/gc_async_mut/jit/jit_runner.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.debug.remote.types`**
- File: `src/lib/gc_async_mut/debug/remote/types.spl`
- Imported by 13 file(s):
  - `src/lib/gc_async_mut/debug/remote/target/riscv32.spl`
  - `src/lib/gc_async_mut/debug/remote/target/arm_cortex_m.spl`
  - `src/lib/gc_async_mut/debug/remote/target/target_info.spl`
  - `src/lib/gc_async_mut/debug/remote/target/x86_64.spl`
  - `src/lib/gc_async_mut/debug/remote/target/riscv64.spl`
  - ... and 8 more
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.env

**`std.gc_async_mut.env.variables`**
- File: `src/lib/gc_async_mut/env/variables.spl`
- Imported by 1 file(s):
  - `src/lib/gc_async_mut/oauth2.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.file_system

**`std.gc_async_mut.file_system.file_ops`**
- File: `src/lib/gc_async_mut/file_system/file_ops.spl`
- Imported by 1 file(s):
  - `src/lib/gc_async_mut/oauth2.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.file_system.permissions`**
- File: `src/lib/gc_async_mut/file_system/permissions.spl`
- Imported by 1 file(s):
  - `src/lib/gc_async_mut/oauth2.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.gpu

**`std.gc_async_mut.gpu.browser_engine.browser_renderer`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`
- Imported by 3 file(s):
  - `src/lib/gc_async_mut/web/browser_session.spl`
  - `src/lib/gc_async_mut/web/browser_session_runtime.spl`
  - `src/lib/gc_async_mut/web/simple_browser_page.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.css`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/css.spl`
- Imported by 1 file(s):
  - `src/app/ui.chromium/engine_merge.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.dom`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`
- Imported by 3 file(s):
  - `src/app/ui.chromium/app.spl`
  - `src/app/ui.chromium/engine_merge.spl`
  - `src/lib/gc_async_mut/web/simple_browser_page.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.dom_accessors`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl`
- Imported by 3 file(s):
  - `src/app/ui.chromium/app.spl`
  - `src/app/ui.chromium/engine_merge.spl`
  - `src/lib/gc_async_mut/web/simple_browser_page.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.layout`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`
- Imported by 2 file(s):
  - `src/app/ui.chromium/engine_merge.spl`
  - `src/lib/gc_async_mut/web/simple_browser_page.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.layout_box`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl`
- Imported by 2 file(s):
  - `src/app/ui.chromium/engine_merge.spl`
  - `src/lib/gc_async_mut/web/simple_browser_page.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.simple_web_renderer`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`
- Imported by 7 file(s):
  - `src/app/ui.browser/renderer.spl`
  - `src/app/wm_compare/emulated_capture.spl`
  - `src/app/wm_compare/simple_html_capture_worker.spl`
  - `src/app/wm_compare/site_corpus_compat.spl`
  - `src/os/compositor/electron_capture.spl`
  - ... and 2 more
- Symbols: (inline/qualified usage — check consumer files)

**`std.gc_async_mut.gpu.browser_engine.text_painter`**
- File: `src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl`
- Imported by 1 file(s):
  - `src/app/wm_compare/site_corpus_layout_report.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.http_client

**`std.gc_async_mut.http_client`**
- File: `src/lib/gc_async_mut/http_client.spl`
- Imported by 1 file(s):
  - `src/lib/gc_async_mut/oauth2.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.gc_async_mut.io

**`std.gc_async_mut.io.event_loop`**
- File: `src/lib/gc_async_mut/io/event_loop.spl`
- Imported by 1 file(s):
  - `src/lib/gc_async_mut/io.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.js.builtins

**`std.js.builtins.array`**
- File: `src/lib/js/builtins/array.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/js/engine/interpreter.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl`
  - `src/lib/gc_async_mut/js/engine/interpreter_eval.spl`
  - `src/lib/nogc_async_mut/js/engine/interpreter_eval.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.js.builtins.json`**
- File: `src/lib/js/builtins/json.spl`
- Imported by 4 file(s):
  - `src/lib/nogc_sync_mut/js/engine/interpreter.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`
  - `src/lib/gc_async_mut/js/engine/interpreter_native.spl`
  - `src/lib/nogc_async_mut/js/engine/interpreter_native.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.js.types

**`std.js.types.ast_types`**
- File: `src/lib/js/types/ast_types.spl`
- Imported by 20 file(s):
  - `src/app/js/main.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_array_methods.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl`
  - ... and 15 more
- Expected symbols: `JsExpression`, `JsStatement`, `SwitchCase`

**`std.js.types.js_types`**
- File: `src/lib/js/types/js_types.spl`
- Imported by 33 file(s):
  - `src/app/js/main.spl`
  - `src/lib/nogc_sync_mut/js/conformance/runner.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_array_methods.spl`
  - `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl`
  - ... and 28 more
- Expected symbols: `JsValue`, `JsObject`, `JsProperty`

**`std.js.types.pair`**
- File: `src/lib/js/types/pair.spl`
- Imported by 27 file(s):
  - `src/app/snpm/cmd_init.spl`
  - `src/app/snpm/cmd_install.spl`
  - `src/app/snpm/cmd_uninstall.spl`
  - `src/app/snpm/cmd_update.spl`
  - `src/app/snpm/manifest.spl`
  - ... and 22 more
- Symbols: (inline/qualified usage — check consumer files)

### std.lib.blink

**`std.lib.blink.dom.interaction_state`**
- File: `src/lib/lib/blink/dom/interaction_state.spl`
- Imported by 1 file(s):
  - `src/lib/blink/css_parser/selector.spl`
- Symbols: (inline/qualified usage — check consumer files)

**`std.lib.blink.dom.node`**
- File: `src/lib/lib/blink/dom/node.spl`
- Imported by 1 file(s):
  - `src/lib/blink/css_parser/selector.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.nogc_sync_mut.game2d

**`std.nogc_sync_mut.game2d.asset.error`**
- File: `src/lib/nogc_sync_mut/game2d/asset/error.spl`
- Imported by 1 file(s):
  - `src/lib/nogc_sync_mut/game2d/config/game_sdn.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.nogc_sync_mut.http_client

**`std.nogc_sync_mut.http_client`**
- File: `src/lib/nogc_sync_mut/http_client.spl`
- Imported by 7 file(s):
  - `src/app/itf/adapter_bitbucket.spl`
  - `src/app/itf/adapter_confluence.spl`
  - `src/app/itf/adapter_outlook.spl`
  - `src/app/itf/adapter_outlook_curl.spl`
  - `src/app/itf/cmd_api.spl`
  - ... and 2 more
- Expected symbols: `types.`

### std.nogc_sync_mut.io

**`std.nogc_sync_mut.io.tls_ffi`**
- File: `src/lib/nogc_sync_mut/io/tls_ffi.spl`
- Imported by 3 file(s):
  - `src/app/ui.web/server.spl`
  - `src/app/ui.web/tls_client.spl`
  - `src/app/ui.web/tls_serve_loop.spl`
- Symbols: (inline/qualified usage — check consumer files)

### std.pe_coff_header

**`std.pe_coff_header`**
- File: `src/lib/pe_coff_header.spl`
- Imported by 2 file(s):
  - `src/compiler/70.backend/linker/pe_inspect.spl`
  - `src/compiler/70.backend/linker/pe_parser.spl`
- Symbols: (inline/qualified usage — check consumer files)

## SKIP Stubs (Not Imported Anywhere)

These 88 stubs are not referenced by any non-stub code. Implement last or defer.

- `app.dap.adapter.remote` → `src/app/dap/adapter/remote.spl`
- `app.hosted_apps.apps.browser_demo.browser_demo_hosted` → `src/app/hosted_apps/apps/browser_demo/browser_demo_hosted.spl`
- `app.hosted_apps.apps.smux.smux_remote` → `src/app/hosted_apps/apps/smux/smux_remote.spl`
- `app.hosted_apps.compositor.hosted_input_backend` → `src/app/hosted_apps/compositor/hosted_input_backend.spl`
- `app.main` → `src/app/main.spl`
- `app.test_daemon.test_manifest` → `src/app/test_daemon/test_manifest.spl`
- `app.test_daemon.test_manifest_scanner` → `src/app/test_daemon/test_manifest_scanner.spl`
- `compiler.00.common.json` → `src/compiler/00.common/json.spl`
- `compiler.weaving.diagnostics` → `src/compiler/weaving/diagnostics.spl`
- `std.common.crypto.constant_time` → `src/lib/common/crypto/constant_time.spl`
- `std.common.layout.box_model` → `src/lib/common/layout/box_model.spl`
- `std.common.llm.content_authority` → `src/lib/common/llm/content_authority.spl`
- `std.common.llm.output_gate` → `src/lib/common/llm/output_gate.spl`
- `std.common.office.file_ops` → `src/lib/common/office/file_ops.spl`
- `std.common.office.undo` → `src/lib/common/office/undo.spl`
- `std.common.privilege.authority_token` → `src/lib/common/privilege/authority_token.spl`
- `std.common.privilege.id_path` → `src/lib/common/privilege/id_path.spl`
- `std.common.privilege.principal` → `src/lib/common/privilege/principal.spl`
- `std.common.privilege.store` → `src/lib/common/privilege/store.spl`
- `std.common.proton_runtime_subsystems` → `src/lib/common/proton_runtime_subsystems.spl`
- `std.common.pure.list` → `src/lib/common/pure/list.spl`
- `std.common.render_scene.scene` → `src/lib/common/render_scene/scene.spl`
- `std.common.rich_text.attributed_text` → `src/lib/common/rich_text/attributed_text.spl`
- `std.common.rich_text.editor` → `src/lib/common/rich_text/editor.spl`
- `std.common.sdn.document` → `src/lib/common/sdn/document.spl`
- `std.common.security.audit_log` → `src/lib/common/security/audit_log.spl`
- `std.common.security.types` → `src/lib/common/security/types.spl`
- `std.common.spm.spm_rpc` → `src/lib/common/spm/spm_rpc.spl`
- `std.common.ui.access` → `src/lib/common/ui/access.spl`
- `std.common.ui.access_adapter` → `src/lib/common/ui/access_adapter.spl`
- `std.common.ui.access_source` → `src/lib/common/ui/access_source.spl`
- `std.common.ui.access_vision` → `src/lib/common/ui/access_vision.spl`
- `std.common.ui.backend` → `src/lib/common/ui/backend.spl`
- `std.common.ui.capability` → `src/lib/common/ui/capability.spl`
- `std.common.ui.capability_policy` → `src/lib/common/ui/capability_policy.spl`
- `std.common.ui.event` → `src/lib/common/ui/event.spl`
- `std.common.ui.glass.theme` → `src/lib/common/ui/glass/theme.spl`
- `std.common.ui.glass.tokens` → `src/lib/common/ui/glass/tokens.spl`
- `std.common.ui.glass_css` → `src/lib/common/ui/glass_css.spl`
- `std.common.ui.ios.builder` → `src/lib/common/ui/ios/builder.spl`
- `std.common.ui.ios.theme` → `src/lib/common/ui/ios/theme.spl`
- `std.common.ui.ios_css` → `src/lib/common/ui/ios_css.spl`
- `std.common.ui.ios_icons` → `src/lib/common/ui/ios_icons.spl`
- `std.common.ui.layout` → `src/lib/common/ui/layout.spl`
- `std.common.ui.lifecycle` → `src/lib/common/ui/lifecycle.spl`
- `std.common.ui.parse.sdn` → `src/lib/common/ui/parse/sdn.spl`
- `std.common.ui.parse.sdn_tree` → `src/lib/common/ui/parse/sdn_tree.spl`
- `std.common.ui.patch_stream` → `src/lib/common/ui/patch_stream.spl`
- `std.common.ui.patch_wire` → `src/lib/common/ui/patch_wire.spl`
- `std.common.ui.reactive` → `src/lib/common/ui/reactive.spl`
- `std.common.ui.session` → `src/lib/common/ui/session.spl`
- `std.common.ui.snapshot_wire` → `src/lib/common/ui/snapshot_wire.spl`
- `std.common.ui.state` → `src/lib/common/ui/state.spl`
- `std.common.ui.style` → `src/lib/common/ui/style.spl`
- `std.common.ui.taskbar_model` → `src/lib/common/ui/taskbar_model.spl`
- `std.common.ui.theme_package` → `src/lib/common/ui/theme_package.spl`
- `std.common.ui.theme_registry` → `src/lib/common/ui/theme_registry.spl`
- `std.common.ui.widget` → `src/lib/common/ui/widget.spl`
- `std.common.ui.window_surface_registry` → `src/lib/common/ui/window_surface_registry.spl`
- `std.common.ui.wine_simpleos_window_bridge` → `src/lib/common/ui/wine_simpleos_window_bridge.spl`
- `std.common.ui.x11_backend_gate` → `src/lib/common/ui/x11_backend_gate.spl`
- `std.common.web.logging` → `src/lib/common/web/logging.spl`
- `std.common.win_fs.acl` → `src/lib/common/win_fs/acl.spl`
- `std.common.win_fs.fs_encoder` → `src/lib/common/win_fs/fs_encoder.spl`
- `std.common.win_fs.window_record` → `src/lib/common/win_fs/window_record.spl`
- `std.common.window_protocol.geometry` → `src/lib/common/window_protocol/geometry.spl`
- `std.common.window_protocol.window_protocol` → `src/lib/common/window_protocol/window_protocol.spl`
- `std.common.wine_gui_hello` → `src/lib/common/wine_gui_hello.spl`
- `std.common.wine_hello_exe` → `src/lib/common/wine_hello_exe.spl`
- `std.common.wine_hello_fixture` → `src/lib/common/wine_hello_fixture.spl`
- `std.common.wine_process_session` → `src/lib/common/wine_process_session.spl`
- `std.common.wine_simpleos_exec_env_gate` → `src/lib/common/wine_simpleos_exec_env_gate.spl`
- `std.common.wine_vm_adapter` → `src/lib/common/wine_vm_adapter.spl`
- `std.hardware.riscv_common.core.riscv_formal` → `src/lib/hardware/riscv_common/core/riscv_formal.spl`
- `std.nogc_sync_mut.js.engine.interpreter_types` → `src/lib/nogc_sync_mut/js/engine/interpreter_types.spl`
- `std.nogc_sync_mut.js.engine.js_error` → `src/lib/nogc_sync_mut/js/engine/js_error.spl`
- `std.nogc_sync_mut.js.engine.lexer` → `src/lib/nogc_sync_mut/js/engine/lexer.spl`
- `std.nogc_sync_mut.js.engine.module_loader` → `src/lib/nogc_sync_mut/js/engine/module_loader.spl`
- `std.nogc_sync_mut.js.engine.parser` → `src/lib/nogc_sync_mut/js/engine/parser.spl`
- `std.nogc_sync_mut.js.engine.runtime` → `src/lib/nogc_sync_mut/js/engine/runtime.spl`
- `std.nogc_sync_mut.js.engine.vm_object_store` → `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl`
- `std.nogc_sync_mut.src.tooling.easy_fix` → `src/lib/nogc_sync_mut/src/tooling/easy_fix.spl`
- `std.nogc_sync_mut.web_framework.controller` → `src/lib/nogc_sync_mut/web_framework/controller.spl`
- `std.nogc_sync_mut.web_framework.flash` → `src/lib/nogc_sync_mut/web_framework/flash.spl`
- `std.nogc_sync_mut.web_framework.form_validation` → `src/lib/nogc_sync_mut/web_framework/form_validation.spl`
- `std.nogc_sync_mut.web_framework.pagination` → `src/lib/nogc_sync_mut/web_framework/pagination.spl`
- `std.nogc_sync_mut.web_framework.route_types` → `src/lib/nogc_sync_mut/web_framework/route_types.spl`
- `std.web.http.server` → `src/lib/web/http/server.spl`

## LOW Priority Stubs (Imported Only by Other Stubs)

None found. All stub importers are real code or stubs are not imported.
