# SMF UI Builder Internals Research
<!-- 2026-06-12 -->

## 1. SMF Emission

**Command:** `bin/simple compile <src.spl> --emit-smf -o out.smf`

Tested on `/tmp/smf_test/hello.spl` (`fn get_answer() -> i64: 42`). Result:

```
Compiled /tmp/smf_test/hello.spl -> /tmp/smf_test/hello2.smf
```

**Minimal SMF size: 179 bytes** (verified across ~100 cached `.smf` stubs in `src/app/*/`.smf`).
The 179-byte floor is consistent — every single stub in the codebase is exactly 179 bytes.

**4 KB feasibility:** YES — a small data-only or single-function module fits comfortably
under 4096 bytes. The 179-byte minimum leaves 3917 bytes of headroom for code + symbol
table + sections. A "dynSMF" constraint of < 4096 bytes per part is realistic for small
leaf modules. Large modules (many symbols, generic template sections) will exceed 4 KB
and must be split.

**Writer:** `src/compiler/80.driver/smf_writer.spl` — `generate_smf_with_all_sections()` and
`build_smf_module()`. Format is sections-first, header-at-EOF-128 (trailer, ZIP-style).

## 2. SMF Format

**Magic:** `[83, 77, 70, 0]` = `"SMF\0"` — defined at:
- `src/compiler/70.backend/linker/smf_header.spl:26` — `val SMF_MAGIC: [u8] = [83, 77, 70, 0]`
- `val SMF_HEADER_SIZE: i64 = 128` (line 27)

**Header layout (128 bytes, v1.1 — trailer at EOF-128):**
- Identification (8): magic[4], version_major, version_minor, platform, arch
- Flags (20): flags, compression, compression_level, section_count, section_table_offset
- Symbols (16): symbol_table_offset, symbol_count, exported_count
- Execution (16): entry_point, stub_size, smf_data_offset
- Hashing (16): module_hash, source_hash
- Hints (12): app_type, window_width, window_height, prefetch_hint, prefetch_file_count
- Reserved (40): padding

**Key flags** (`smf_header.spl:30-34`): `SMF_FLAG_EXECUTABLE=0x0001`, `SMF_FLAG_RELOADABLE=0x0002`,
`SMF_FLAG_DEBUG_INFO=0x0004`, `SMF_FLAG_PIC=0x0008`, `SMF_FLAG_HAS_STUB=0x0010`

**Reader/writer files:**
- `src/compiler/70.backend/linker/smf_header.spl` — SmfHeader struct, constants
- `src/compiler/70.backend/linker/smf_writer.spl` — linker-layer writer
- `src/compiler/80.driver/smf_writer.spl` — driver-layer with template/metadata sections
- `src/compiler/70.backend/linker/smf_reader.spl` — reader
- `src/compiler/99.loader/loader/smf_cache.spl` — runtime cache/mmap

**v1.1 layout:** sections written first, then section table, symbol table, string table,
finally 128-byte header trailer. Section entry size = 64 bytes.
Optional sections: code, TemplateCode, TemplateMeta, `.note.sdn`, `.note.deps`,
`.drv_manifest`, `.launch_meta`.

**DynSmf runtime:** `src/os/smf/dynsmf_session.spl` — `DynSmfArtifactStatus` checks
`magic_hex` and `byte_count`; `smf_dlopen_checked` from `src/os/smf/smf_dynlib.spl`.

## 3. dynSMF Build Lane

**Build plan declaration:** `src/os/smf/dynsmf_session.spl:67-74` —
`fn dynsmf_default_manifest() -> [DynSmfManifestEntry]`

Six manifest entries and their source→output mappings
(`dynsmf_manifest_source_path`, line 92):

| library_id     | source_path                                           | output_path                      |
|----------------|-------------------------------------------------------|----------------------------------|
| file_io        | src/lib/nogc_sync_mut/io/file.spl                     | build/dynsmf/file_io.smf         |
| net_io         | src/lib/nogc_sync_mut/net.spl                         | build/dynsmf/net_io.smf          |
| render2d       | src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl    | build/dynsmf/render2d.smf        |
| web_renderer   | src/app/ui.render/html_widgets.spl                    | build/dynsmf/web_renderer.smf    |
| gui_renderer   | src/app/ui.web/backend.spl                            | build/dynsmf/gui_renderer.smf    |
| tui_renderer   | src/app/ui.render/tui_widgets.spl                     | build/dynsmf/tui_renderer.smf    |

**Adding a new entry:** add a `DynSmfManifestEntry(...)` to the array in `dynsmf_default_manifest()`
(line 67) and add a matching `if entry.id == "new_id": return "src/..."` branch in
`dynsmf_manifest_source_path()` (line 92).

**Check script:** `scripts/check/check-low-dependency-dynsmf-build-plans.shs` — runs
`bin/simple run` on a generated probe that calls `dynsmf_build_plans(dynsmf_default_manifest())`,
then calls `bin/simple compile <source_path> -o <output_path>` for each ready plan.

**Startup autoload:** `src/app/startup/dynsmf_autoload.spl` —
`dynsmf_startup_session(args, session_id)` reads `SIMPLE_DYNSMF` / `SIMPLE_DYNSMF_DISABLE`
env vars, calls `dynsmf_session_queue_missing_background_compiles()` for any SMF not yet
on disk, then `dynsmf_session_autoload_checked()` to dlopen ready ones.

## 4. HTML and CSS Parsers

**HTML parser facade:** `src/lib/nogc_sync_mut/html_parser_utils.spl` — compatibility
re-export of `std.gc_async_mut.html_parser_utils.*`. Refactored from 1,688 lines into
7 focused sub-modules: Types, Lexer, Parser, DOM, Entities, Serializer, Utilities.
Sub-modules live under `src/lib/gc_async_mut/html/` (directory confirmed, API via
`grep` returned no direct pub fn — symbols are re-exported via `export use`).

**HTML render-to-pixels APIs** (best reusable, `gc_async_mut` tier):
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl:46`
  `pub fn simple_web_render_html_to_scene(html: text, width: i32, height: i32) -> SimpleWebRenderScene`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl:67`
  `pub fn simple_web_render_html_to_pixels(html: text, width: i32, height: i32) -> [u32]`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_file_renderer.spl:20`
  `pub fn simple_web_render_html_to_rgba_bytes(html: text, width: i64, height: i64) -> [u8]`

**No dedicated CSS parser** found as a standalone Simple module. CSS is consumed inline
by the browser engine (`simple_web_renderer.spl`) and via pre-authored glass/iOS CSS
string-returning functions in `src/lib/common/ui/glass_css*.spl` and `ios_css.spl`.
The `web_render_adapter_request()` API in `src/lib/common/ui/web_render_api.spl:82`
accepts `css: text` as a plain string parameter. For a compile-time CLI, CSS should be
treated as an opaque text blob passed into the render APIs rather than parsed separately.

## 5. src/lib/common/ui/ Catalog

**`widget_kind.spl`** (`src/lib/common/ui/widget_kind.spl`) — `enum WidgetKind` with
42 variants: Panel, Text, List, Table, Progress, Menubar, Statusbar, Input, Tabs,
Button, Checkbox, RadioButton, Dropdown, Textfield, Image, Divider, Dialog, Tooltip,
Tree, Treenode, Scroll, Textarea, Heading, Label, NavigationBar, TabBar, Card, Switch,
SegmentedControl, SearchBar, GlassTitleBar, Sidebar, CommandBar, WorkspaceTabs,
CommandPalette, Toast, SheetModal, ContextMenu, Inspector, UtilityRail, StatusChip,
SelectionPill, EmptyState. Each has a `to_wire() -> text` wire name. **This is the
canonical element-to-widget mapping target for HTML→SMF compilation.**

**`html_window.spl`** — backend-neutral HTML fragment helpers for MDI window bodies.
Key fns: `html_window_base_css()`, `html_window_content_with_titlebar_widgets(title, body_html, titlebar_widgets, extra_css)`, `html_titlebar_button(action, label)`, `html_escape()`, `html_picture()`, `html_pre_block()`.

**`mobile_html_gen.spl`** — structured HtmlNode builder:
`html_node(tag, attrs, children)`, `html_leaf(tag, attrs, text_content)`,
`html_void(tag, attrs)`, `attr(key, value)`, `html_node_render(node)`,
`html_gen_document(title, body_html, css)`.

**`glass_css*.spl`** — pre-authored CSS string factories for glass-morphism design system
(components, shell, surfaces, glass/).

**`parse/sdn.spl`** — `.ui.sdn` (Simple Data Notation) parser with
`parse_to_flat(source: text) -> [FlatEntry]`, `render_node_html(entries, path, depth)`,
`build_html_page(title, theme, body_html)`.

**`web_render_api.spl`** — `web_render_adapter_request(target, surface_id, title, body_html, css, js, viewport_w, viewport_h) -> WebRenderRequest` — primary request builder for feeding HTML+CSS into the render pipeline.

**`builder.spl`** — UI tree builder (pre-compiled `.smf` available as `builder.smf`).

## 6. CLI App Conventions

**Pattern** (from `src/app/todo_gen/main.spl:238`):

```simple
use std.cli.cli_util (get_cli_args, parse_csv_fields)

fn main() -> i64:
    val args = get_cli_args()   # returns [text]
    var ai = 0
    while ai < args.len():
        val arg = args[ai]
        # parse flags / positional args
        ai = ai + 1
    0
```

Run via: `bin/simple run src/app/myapp/main.spl -- --flag value`

Args after `--` are passed as `get_cli_args()` result. No framework required — iterate
`[text]` directly. Log options helper available via `std.cli.log_modes`.
