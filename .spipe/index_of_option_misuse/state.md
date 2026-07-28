# Lane IDXFIX2 — `index_of` / `find` / `last_index_of` results treated as Option

Bug: `doc/08_tracking/bug/option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`
Predecessor: lane IDXFIX (its state is preserved in git history of this file).

## Contract re-derived on the current binary (`build/idxfix2/*.spl`)

`bin/simple run` and `SIMPLE_NO_JIT=1 bin/simple run` gave **identical** results for
every probe below, so this defect is not engine-specific on the current toolchain.

| expression (`s = "hello"`, found=1, miss=-1) | result | verdict |
|---|---|---|
| `s.index_of("ell")` / `s.index_of("zzz")` | `1` / `-1` | plain `i64`, `-1` sentinel |
| `match idx: Some(i)` | **always** takes `Some`, binds **nil** | broken, found *and* miss |
| `idx == nil` | **always false** | dead guard — not-found path never runs |
| `idx != nil` | **always true** | guard never rejects `-1` |
| `idx ?? N` | returns raw `idx` (`-1` leaks) | no-op coalesce |
| `idx.unwrap()` (found) | **`nil`** | corrupt |
| `idx.unwrap()` (miss) | `<value:0xffffffffffffffff>` | tag box leak |
| `s.find(x).unwrap_or(-1)` | `<value:0x6>` / `<value:0xff..ff>` | tag box leak |
| `"a/b/c".last_index_of("/")` = 3, `match: Some/nil` | takes **nil** arm | **INVERTED** |
| `"abc".last_index_of("/")` = -1, `match: Some/nil` | takes **Some**, binds nil | **INVERTED** |

`last_index_of` inverts where `index_of` always-Somes — but both are plain `i64`.
The predecessor lane's claim that `last_index_of` is "correctly Option-shaped" is
**WRONG**: `src/lib/text.spl:61` declares `-> i64?` but the *builtin* intercepts
first (`interpreter/eval_methods.spl:459` returns `val_make_int(... ?? -1)`,
`compiler/cg_expr.spl:555` emits `spl_str_last_index_of`), so callers see a raw
`i64`.

## Site table (this lane's own scan; excludes lane-boundary paths)

Scan: `build/idxfix2/window_hits.txt` (producer → `Some(`/`unwrap_or` within 6
lines) and `build/idxfix2/nilcmp.txt` (producer → `== nil` / `!= nil` / `??` /
`.unwrap*` / `.is_some` on the same variable within 14 lines).

### Already correct (false positives — no edit)

| file:line | shape | why safe |
|---|---|---|
| src/app/portal/server.spl:407,411 | `Some(trimmed[eq+1:])` | `Some(...)` is the *return* value; guard is `eq > 0` |
| src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http_client/types.spl | `Some(build_url(...))` | guard is `last_slash >= 0` |
| src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl:399 | `Some(Url.create(...))` | guarded by `contains("/")`, raw int use |
| src/lib/gc_async_mut/web/browser_session_html.spl:269 | `Some(rest.substring(...))` | guard is `rel_end >= 0` |
| src/lib/gc_async_mut/web/browser_session.spl:1022 | `Some(rest.slice(...))` | guard is `quote < 0: return nil` |
| src/lib/nogc_async_mut/http/request.spl:103 | `Some(err)` | scrutinee is `check_header_size`, a real Option |
| src/lib/{nogc_sync_mut,nogc_async_mut}/cli/simple_parser_api.spl | `Some(option_def)` | scrutinee is `find_option_by_long`, a real Option |
| src/lib/nogc_sync_mut/src/exp/config.spl:282 | `case Some(Str(sv))` | scrutinee is `lookup_path`; `end` guarded by `end < 0` |
| src/app/interpreter/lazy/lazy_seq_spec.spl:229,382 | `assert found == Some(10)` | `Iterator.find`, a real Option |
| src/app/llm_caret/redact.spl:54, src/app/simple_lsp_mcp/json_helpers.spl:58 | — | comments describing this very bug |

### Real sites repaired by this lane

| # | file:line | shape | not-found behaviour preserved |
|---|---|---|---|
| 1 | src/app/mcp/api_tools.spl:54,59,64,70 | `(idx ?? 0)` leaks `-1` into `substring` | fall back to offset `0` as the `?? 0` intended |
| 2 | src/lib/nogc_async_mut/mcp/api_tools.spl:79,84,89,95 | same | same |
| 3 | src/lib/nogc_async_mut/mcp/resources.spl:690 | `(q_idx ?? 0)` | `?` absent ⇒ no query split |
| 4 | src/lib/nogc_sync_mut/resource_tracker.spl:300,305 | `start_idx ?? 0`, `end_idx ?? (len-1)` | explicit fallbacks kept |
| 5 | src/lib/gc_async_mut/resource_tracker.spl:300,305 | same | same |
| 6 | src/lib/nogc_async_mut/resource_tracker.spl:300,305 | same | same |
| 7 | src/lib/nogc_sync_mut/process_monitor.spl:42 | `last_paren_idx ?? 0` | fallback `0` kept |
| 8 | src/lib/gc_async_mut/process_monitor.spl:42 | same | same |
| 9 | src/lib/nogc_async_mut/process_monitor.spl:42 | same | same |
| 10 | src/lib/nogc_sync_mut/dependency_tracker/graph.spl:95 | `path.index_of(module) ?? 0` | fallback `0` = whole path |
| 11 | src/lib/nogc_async_mut/dependency_tracker/graph.spl:95 | same | same |
| 12 | src/app/debug/remote/protocol/trace32.spl:468 | `if colon_idx != nil:` always true | skip the line when no `:` |
| 13 | src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl:434 | same | same |
| 14 | src/lib/nogc_async_mut/debug/remote/protocol/trace32.spl:434 | same | same |
| 15 | src/app/llm_caret/claude_full/constants/files.spl:14 | `if dot == nil:` dead | return the early-out value |
| 16 | src/lib/nogc_sync_mut/http_server/mime.spl:91 | `if dot_idx == nil:` dead | default mime type |
| 17 | src/lib/nogc_sync_mut/ui_test/parse.spl:132,136,142,150,156,217 | `== nil` / `!= nil` | break / skip as written |
| 18 | src/lib/nogc_sync_mut/ui_test/client.spl:250 | `if contains_idx != nil:` always true | assertion must fail on miss |
| 19 | src/lib/nogc_sync_mut/ui_test/http.spl:50 | `if idx == nil:` dead | return whole response |
| 20 | src/app/interpreter/utils/path_resolution.spl:164 | `idx.?` + `idx.unwrap()` | `"."` when no `/` |
| 21 | src/app/mcpgdb/debug_backend_common.spl:112 | `last_index_of` + `match Some(idx)` | leave output unstripped |
| 22 | src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:543 | `last_index_of` + `match Some(i)` | `end_line = start_line` |
| 23 | src/os/services/launcher/launcher_registry.spl:351,364 | `last_index_of` + `case Some(idx)` | whole path as basename |
| 24 | src/os/apps/shell/_ShellTools/text_tools.spl:141 | `== nil` + `.unwrap()` | whole trimmed content |

### Also repaired — `.?`-truthiness residue left by lane NILQ

`.?` on an `i64` is plain truthiness, so it is wrong at **both** ends: false at
index `0`, true at `-1`. Sites half-repaired as `if x.? and x >= 0:` still drop
a genuine match at index 0.

| # | file:line | shape |
|---|---|---|
| 25 | src/lib/nogc_async_mut/http_server/parser.spl:94,106,128,223,235 | `.? and …` — `line_end == 0` (end-of-headers) was unreachable |
| 26 | src/lib/nogc_sync_mut/http/accept_encoding.spl:34,110,125 | `.? and …` |
| 27 | src/lib/gc_async_mut/http/accept_encoding.spl:34,110,125 | same |
| 28 | src/lib/nogc_async_mut/http/accept_encoding.spl:34,110,125 | same |

### Deferred — outside this lane's owned paths

| file:line | owner |
|---|---|
| src/os/tools/net/wget_tool.spl:31,41,54,68 (4× `if val Some(i) = …`) | URL-parsing exclusion |
| src/lib/{nogc_sync_mut,nogc_async_mut}/ftp_utils.spl:501,508 (`at_idx.?` with **no** `>= 0`) | URL-parsing exclusion |
| src/lib/nogc_async_mut/http_server/proxy.spl:310 (`qmark.? and qmark >= 0`) | URL-parsing exclusion |
| src/os/services/llm/_McpOsServer/helpers.spl:56,63,72,80,83 | lane UIQUERY (still shows `== nil` / `!= nil` guards) |
| src/lib/common/ui/parse/sdn.spl:38, sdn_tree.spl:43 (`index_of(n) ?? -1`) | lane UIQUERY (benign — `?? -1` is a no-op that yields the right value) |

## Repair rule

`>= 0` = found, `< 0` = not found. Every rewrite keeps the *existing* not-found
branch verbatim; only the test changes.

## Other sentinel-returning functions checked

- `text.index_of` / `find` / `find_str` — plain `i64`, `-1`. (builtin,
  `eval_methods.spl:450`)
- `text.last_index_of` / `rfind` — plain `i64`, `-1` (builtin shadows the
  `-> i64?` declaration in `src/lib/text.spl:61`).
- `[T].index_of` — plain `i64`, and additionally returns `-1` even when the
  element **is** present (predecessor lane, `build/idxfix/arr2.spl`). Separate
  defect, not fixed here.
- `Dict.get(k) ?? default` — different family (native `Dict.get` corruption,
  `.claude/rules/code-style.md`); untouched.

## Verification

A/B harnesses (`build/idxfix2/verify2.spl`, `verify3.spl`, `verify4.spl`) run the
repaired logic next to the verbatim pre-fix logic from `git show HEAD:<file>`:

| function | before | after |
|---|---|---|
| `api_tools.extract_nested_string` on valid JSON | `""` — never extracted anything | `v1` |
| `http_server/parser` blank line = end of headers | `need-more` — terminator unreachable | `END-OF-HEADERS` |
| `ui_test/client` contains-assertion on a miss | `true` — could never fail | `false` |
| `ui_test/http.extract_body`, no `\r\n\r\n` | `"defgh"` — sliced from offset 3 | `""` |
| `mime_from_path("noext")` | whole path used as the extension | `application/octet-stream` |
| `accept_encoding` q-value `".5"` | `nodot` → q parsed as 0 | `int=[] frac=[5]` |
| `parent_dirname("/b")` | `""` | `"/"` |
| `resource_tracker.extract_quoted_value` | unchanged (accidentally equivalent) | unchanged |
| `trace32` address-prefix strip | unchanged (accidentally equivalent) | unchanged |

Spec runs (per file, `Results:` line is authoritative):

| spec | verdict |
|---|---|
| test/01_unit/app/lsp_handlers_spec.spl | 8 total, 8 passed, 0 failed |
| test/unit/lib/nogc_async_mut/ui_test/ui_test_facade_spec.spl | 1 total, 1 passed, 0 failed |
| test/unit/app/debug/remote/trace32_client_spec.spl | 30 total, 30 passed, 0 failed |
| test/01_unit/app/mcp_unit/provider_mime_spec.spl | 26 total, 26 passed, 0 failed |
| test/01_unit/compiler_core/interpreter/interp_resource_tracker_spec.spl | 18 total, 18 passed, 0 failed |

**No covering spec exists** for: `http/accept_encoding.spl`,
`http_server/parser.spl`, `http_server/mime.spl`, `process_monitor.spl`,
`dependency_tracker/graph.spl`, `path_resolution.spl`, `launcher_registry.spl`,
`mcp/api_tools.spl`, `_ShellTools/text_tools.spl`,
`llm_caret/.../constants/files.spl`. Those rest on the A/B harness only.

Engines: every probe was run under both `bin/simple run` and
`SIMPLE_NO_JIT=1 bin/simple run` and produced identical output, so neither
engine disagrees on the repaired code.
