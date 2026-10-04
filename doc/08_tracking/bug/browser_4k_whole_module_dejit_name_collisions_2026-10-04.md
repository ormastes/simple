# Simple Browser at 4K runs entirely in the tree-walk interpreter (whole-module de-JIT from bare-name collisions)

- Date: 2026-10-04
- Status: **OPEN. Seven collisions fixed by renaming. The last known blocker is in `net/h1_client.spl` (network-code owner).**
- Related: `lint_dejits_whole_program_span_struct_collision_2026-08-18.md` (same
  seed limitation: the run/JIT lane flattens every import into one bare-name
  namespace). `exec_core.rs` documents why the `SIMPLE_JIT_DUP_STRUCT_FEED`
  consensus fallback must stay off.
- Binary for every number: a Rust seed built from `src/compiler_rust` at
  `73150c2673f` (`cargo build --profile bootstrap -p simple-driver`, sha256
  `056afef47c8d…`). The deployed `bin/simple` (Sep 27,
  `f2b3edd25068…`) cannot run origin/main at all, because it predates
  `faa15917adc` (host `@when` stripping). It fails to parse
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl`. Host: M4, 24 GB, macOS 25.5.

## Symptom

`simple run src/app/browser/main.spl simple://home` prints
`[jit-fallback] HIR lowering error: ... whole module dropped to the interpreter`.
At the new 4K default (3840x2160) the headless render does not finish
within `timeout 900`. The run was killed at **900.2 s wall, 734.8 s user, 2.79 GB max RSS**.

| viewport | wall | user | max RSS | engine |
|---|---|---|---|---|
| hello-world `.spl` (loader floor) | 0.08 s | 0.02 s | 23 MB | JIT |
| 64x36 | 51.7 s | 36.5 s | 1.65 GB | interpreter |
| 384x216 (live lane) | 60.5 s | 53.3 s | 1.62 GB | interpreter |
| 3840x2160 (vulkan lane) | >900 s (killed) | 734.8 s | 2.79 GB | interpreter |

The marginal cost is about **0.2 ms of interpreted work per pixel**: going from 64x36 to 384x216
adds 16.8 s user for 80.6k pixels. Most of the ~1.6 GB floor comes from loading
the browser's module graph into the interpreter. Hello world is 23 MB.

## Root cause

The flattened module registers structs and functions by bare name. When a name has two
or more definitions, a field read or return type resolves against the wrong layout. HIR
lowering then fails, and the WHOLE flattened program is demoted.

Each strict run (`SIMPLE_JIT_STRICT=1`) exposed the next collision:

| collision | resolved to | fix (renamed side) |
|---|---|---|
| `TextMetrics.char_count` | `common/layout/text_metrics.spl` | engine2d `helpers_text.TextMetrics` -> `Engine2dTextMetrics` |
| `HtmlToken.token_kind` | `blink/html_parser/token.spl` | browser_engine -> `WebHtmlToken` |
| `ComputedStyle`, `LayoutContext`, `BoxShadow` | blink copies | browser_engine -> `Web*` |
| `hex_byte` returns `text` | `jit_util.hex_byte` | `dom_color` -> `css_hex_byte` / `css_hex_nibble` / `css_hex_digit` |
| `RenderScene.viewport_w` | `common/render_scene` | browser_engine `layout.spl` stub -> `LayoutPaintScene` |
| non-generic `Pair` | (`custom_properties`) | -> `CssVarPair` |
| `BrowserError` / `Logger` / `script_error` / `BrowserResult` (warnings) | JS engine `js_error` copies | JS side -> `JsBrowserError` / `JsLogger` / `js_script_error` / `JsBrowserResult` |

**Remaining blocker, not fixed here:** this lane must not edit network code.

- `gc_async_mut/gpu/browser_engine/net/h1_client.spl` `parse_http_response_bytes`:
  `struct 'ANY' field 'first'`. The type `Pair<[u8],[u8]>` lowers to ANY
  inside the full browser graph, even with an explicit annotation. A
  standalone probe of the same shape lowers fine.
- The same file in isolation (`use ...net.h1_client.*`) also fails in
  `H1Client.request` with `struct 'ANY' field 'tls_conn'`.

## Diagnostic added

`SIMPLE_SEED_RETURN_TYPE_DEBUG=1` now also prints
`lowering error in function <name>: <error>` for any body-lowering failure
(`hir/lower/module_lowering/function.rs`). The whole-module message names
only the entry file. Without this, finding `hex_byte` took a blind search.

## Other findings

- origin/main `gc_async_mut/gpu/engine2d/draw_ir_adv.spl` called
  `draw_ir_command_has_unsupported_v4_state`, but that function does not exist on main or on
  `release/1.0`. It, and the V4 `affine_transform` / `raster_policy` fields it
  reads, live only in `1ef63f7a985`. Every browser render failed with
  `E1002 function not found`. Main's `DrawIrCommand` has no V4 state, so this branch removes the call.
  The guard was vacuous on main.
- JIT `for p in px` over a 3840x2160 `[u32]` takes **1.27 s**. An indexed `while` loop
  writing the same array takes **39 ms**: the `for`-in loop is about 30x slower on the JIT path. Not fixed.
