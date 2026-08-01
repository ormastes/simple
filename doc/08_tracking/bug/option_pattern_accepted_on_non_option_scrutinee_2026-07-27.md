# Bug: `Some(_)` patterns and `.unwrap_or` silently accepted on NON-Option values

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent wrong answers; type error degraded into bad data; engines disagree)
- **Found by:** lane OPTNIL, reproduced independently by the coordinator
- **Reconstructed:** the lane's original doc was clobbered off disk by a parallel
  session before landing; this is rewritten from the lane report plus the
  coordinator's own reproduction.

## Not what it first looked like

This was reported as "Option payloads bind as nil". That framing is **wrong** —
real `Option<T>` is correct on both engines for payloads `0, 1, 3, -7,
123456789`, across `match` / `if val` / `unwrap_or`, for
`Option<i64>`, `Option<text>` and `Option<struct>`. The prior-art
"JIT `Option<i64>` payload 3 reads as None" collision did **not** reproduce.

## The actual defect

`text.index_of` returns a **plain `i64`**, not `Option<i64>` — proven by
`idx + 1 == 7` with no unwrap. The compiler nonetheless **accepts `Some(_)`
patterns and `.unwrap_or` on non-Option receivers instead of erroring**.

A bare `val n = 6` reproduces every symptom with no `index_of` involved, so the
hole is in **type checking**, not in the producer. One raw value yields three
different wrong answers, because each consumer misdecodes the untagged scalar its
own way — and the two engines disagree:

| expression (`n` is a bare `i64` = 6) | JIT | interpreter |
|---|---|---|
| `match n: Some(i)` | takes the `Some` arm, binds **nil** | matches **neither arm — not even the `_` wildcard** |
| `n.unwrap_or(-99)` | **`<value:0x6>`** (tag box leaked into text) | `6` (returns the receiver) |
| `if val Some(k) = n` | branch **taken**, binds **nil** | not taken |
| bare `i64` passed through an `Option<i64>` **parameter** | binds **3** — a plausible wrong integer (`6>>1`) | falls through |
| `None.to_text()` | `nil` | **errors** |

The interpreter failing to match `_` is itself a second defect: a wildcard arm
must be unconditional.

## Where

- ~~`src/compiler/10.frontend/core/interpreter/eval_methods.spl:107` — Option
  handling is gated on `kind == VAL_STRUCT`, so a raw `i64` misses every branch
  and `unwrap_or` (:117) falls through returning the receiver.~~
  **NOW-WRONG (2026-08-01) — this described DEAD CODE.** `eval_methods.spl` was
  a duplicate shadowed by the package-local `_EvalOps` copies and was deleted in
  `f97dfbbb8ee`. Re-derived against the live `eval_method_call`
  (`_EvalOps/call_method_eval.spl:567-654`): it has **no Option/Result built-in
  method block at all**. There is no `unwrap` / `unwrap_or` / `is_some` /
  `is_none` / `unwrap_err` / `is_ok` / `is_err` arm anywhere in the live
  interpreter (`grep '"unwrap"' src/compiler/10.frontend/core/interpreter/`
  returns nothing). Its only `kind == VAL_STRUCT` branches are the `__dict`
  table and a user-method `func_table_lookup`, after which it hits
  `eval_set_error("no method '<name>' on struct")`. So the mechanism recorded
  here — "gated on `VAL_STRUCT`, raw `i64` misses every branch, `unwrap_or`
  returns the receiver" — is **not** the live pure-Simple behaviour. The live
  behaviour for a *struct* Option is a hard error, and for a raw `i64` receiver
  it is `no method 'unwrap_or' on int`. **The user-visible symptom this bug
  reports (`<value:0x6>` leaking from `unwrap_or`) therefore comes from the MIR
  lowering below, not from the interpreter** — which strengthens, not weakens,
  the `rt_unwrap_or_self` root cause. Whether the deleted block ever ran is
  UNKNOWN: the sabotage proof covered `eval_text_method`, whose sole call site
  is inside `_EvalOps`; `eval_method_call`'s external caller is
  `eval.spl:301`, so resolution there was never measured. **What would settle
  it:** nothing anymore — only one definition survives. **What is actionable:**
  if any Simple source calls `.unwrap()`/`.is_some()` on an Option struct under
  the pure-Simple interpreter, it errors today. That gap should be filed and
  fixed on `_EvalOps/call_method_eval.spl`, not rediscovered from the deleted
  file.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:388-396` —
  `option_payload_or_self` emits **`rt_unwrap_or_self`** ("return the receiver if
  it is not an Option"), typed `i64` while the value stays tag-boxed, producing
  `<value:0x6>`. Also :560, :598 and `cranelift_codegen_adapter.spl:1276`.

**That `_or_self` fallback is the design decision that converts a type error into
a silent wrong answer.**

## Blast radius

In owned `src/**`: 11,410 `Some(`, 911 `if val Some(`, 1,168 `.index_of(`.
**17 sites confirmed dangerous** — a bare-`i64` `index_of` result fed into an
Option form — including **4 in `src/lib/nogc_sync_mut/mcp_sdk/core/jsonrpc.spl`**.
Those 4 are the direct cause of the LLM lane's "every MCP tool argument silently
arrived empty" (`_extract_arg` returned `""` for every key). Causal chain closed.

## Reproduce

```
bin/simple run build/optnil_verify.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/optnil_verify.spl
```

## Interim mitigation

At the 17 sites, test `index_of`'s real `-> i64` contract directly:
`if i >= 0:` — do not destructure it as an Option.

## Why no fix landed

Tightening this changes compile behaviour at 11,410 `Some(` sites and needs a
staged warn→error migration; and the primary hole is in a compiler tree where
other lanes were live. A regression spec was also deliberately not added: it
would fail against `main` until the fix lands.

## Next step

1. Decide the contract: either `index_of` returns `Option<i64>` (and callers
   migrate) or it stays `i64` and Option forms on non-Option scrutinees become a
   **compile error**. The current middle ground is the bug.
2. Delete or gate `rt_unwrap_or_self` so a non-Option receiver is rejected rather
   than silently passed through.
3. Fix the interpreter's wildcard arm so `_` always matches.
4. Repair the 17 confirmed sites, starting with `jsonrpc.spl`.

## Sites repaired

### Contract, re-measured (lane IDXFIX2, `build/idxfix2/*.spl`)

`bin/simple run` and `SIMPLE_NO_JIT=1 bin/simple run` gave **identical** results
for every probe, so on the current toolchain this defect is not engine-specific.

| expression (`s = "hello"`; found = 1, miss = -1) | result |
|---|---|
| `match idx: Some(i) / nil` | **always** `Some`, binds **nil** |
| `idx == nil` | **always false** — the not-found branch is dead code |
| `idx != nil` | **always true** — the guard never rejects `-1` |
| `idx ?? N` | returns raw `idx`; `-1` leaks through |
| `idx.?` | **truthiness** — false at index `0`, true at `-1` (inverted at both ends) |
| `idx.unwrap()` | `nil` when found; `<value:0xff..ff>` when not |
| `s.find(x).unwrap_or(-1)` | `<value:0x6>` / `<value:0xff..ff>` |
| `"a/b/c".last_index_of("/")` = 3, matched as Option | takes the **nil** arm |
| `"abc".last_index_of("/")` = -1, matched as Option | takes the **Some** arm, binds nil |

**`text.last_index_of` / `rfind` are also plain `i64`.** `src/lib/text.spl:61`
declares `-> i64?`, but the builtin intercepts first
(`_EvalOps/access_literal_assign_eval.spl:259-268` returns
`val_make_int(s.last_index_of(needle))`; `compiler/cg_expr.spl:555` emits
`spl_str_last_index_of`), so callers see a raw `i64`. Any earlier note calling
`last_index_of` "correctly Option-shaped" is wrong.

> **Citation corrected 2026-08-01 — conclusion holds, history did not.** This
> cited `eval_methods.spl:459`, which was dead code. Two corrections: (1) the
> live arm lives in `_EvalOps/access_literal_assign_eval.spl`; (2) between
> 2026-07-27 and 2026-08-01 the live text-method table had **no**
> `last_index_of`/`rfind` arm at all — so "the builtin intercepts first" was
> false for the interpreter lane during that window; `last_index_of` fell
> through to `eval_set_error` and returned `-1`/`VAL_NONE`. It became true
> when `f97dfbbb8ee` added the arm. The **raw-`i64`, `-1`-for-miss contract is
> confirmed** on the live code, and the `?? -1` the old citation quoted was
> deliberately dropped (it was dead on a miss and corrupted a genuine hit at
> index 3, the nil sentinel). See
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

### Repaired (lane IDXFIX2 — 28 files)

Rule applied: `>= 0` = found, `< 0` = not found; each site's existing not-found
branch was kept verbatim, only the test changed.

| file | shape |
|---|---|
| `src/app/mcp/api_tools.spl`, `src/lib/nogc_async_mut/mcp/api_tools.spl` | `.? == false` guard + `(idx ?? 0)` (4 each) |
| `src/lib/nogc_async_mut/mcp/resources.spl` | `q_idx.?` + `(q_idx ?? 0)` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/resource_tracker.spl` | `.? == nil` + `?? 0` / `?? (len-1)` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/process_monitor.spl` | `.? == nil` + `?? 0` |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http/accept_encoding.spl` | `.? and …` (3 each) |
| `src/lib/nogc_async_mut/http_server/parser.spl` | `.? and …` (5) |
| `src/lib/nogc_sync_mut/http_server/mime.spl` | `dot_idx == nil` |
| `src/lib/nogc_sync_mut/ui_test/{parse,client,http}.spl` | `== nil` / `!= nil` (8) |
| `src/lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/graph.spl` | `index_of(x) ?? 0` |
| `src/{app,lib/nogc_sync_mut,lib/nogc_async_mut}/debug/remote/protocol/trace32.spl` | `colon_idx != nil` |
| `src/app/llm_caret/claude_full/constants/files.spl` | `dot == nil` |
| `src/app/interpreter/utils/path_resolution.spl` | `idx.?` + `idx.unwrap()` |
| `src/app/mcpgdb/debug_backend_common.spl` | `last_index_of` + `match Some(idx)` |
| `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` | `last_index_of` + `match Some(i)` |
| `src/os/services/launcher/launcher_registry.spl` | `last_index_of` + `case Some(idx)` (2) |
| `src/os/apps/shell/_ShellTools/text_tools.spl` | `== nil` + `.unwrap()` |

### Live failures the repairs removed (A/B, `build/idxfix2/verify*.spl`)

| function | before | after |
|---|---|---|
| `api_tools.extract_nested_string` on valid JSON | `""` — **never extracted anything** | `v1` |
| `http_server/parser` blank line = end of headers | `need-more` — **terminator unreachable**, headers never finished | `END-OF-HEADERS` |
| `ui_test/client` contains-assertion on a miss | `true` — **the assertion could never fail** | `false` |
| `ui_test/http.extract_body` with no `\r\n\r\n` | `"defgh"` — body sliced from offset 3 of an unrelated response | `""` |
| `mime_from_path("noext")` | treated the whole path as the extension | `application/octet-stream` |
| `accept_encoding` q-value `".5"` | `nodot` → q parsed as 0 | `int=[] frac=[5]` |

### Deferred (outside this lane's owned paths)

| file | owner |
|---|---|
| `src/os/tools/net/wget_tool.spl:31,41,54,68` (`if val Some(i) = …`) | URL-parsing lane |
| `src/lib/{nogc_sync_mut,nogc_async_mut}/ftp_utils.spl:501,508` (`at_idx.?` with no `>= 0`) | URL-parsing lane |
| `src/lib/nogc_async_mut/http_server/proxy.spl:310` (`qmark.? and qmark >= 0`) | URL-parsing lane |
| `src/os/services/llm/_McpOsServer/helpers.spl:56,63,72,80,83` | lane UIQUERY |
| `src/lib/common/ui/parse/{sdn,sdn_tree}.spl` (`index_of(n) ?? -1`) | lane UIQUERY — benign no-op |

### Separate defects found while repairing

1. **`text[a..b]` (double-dot range slice) is corrupt.** `"/a/b"[0..2]` yields a
   text whose `.len()` is `-1` and which makes string interpolation swallow the
   entire output line; `[0:2]` and `.slice(0,2)` are correct. Pre-existing —
   it had silently broken `parent_dirname` in
   `src/app/interpreter/utils/path_resolution.spl`, now switched to `[0:idx]`.
2. **`[T].index_of(v)` returns `-1` even when the element is present**
   (`build/idxfix/arr2.spl`). Array `index_of` looks unimplemented; distinct
   from the Option-shape bug and not fixed here.
3. `.?` on an `i64` is plain truthiness, so it is wrong at *both* ends: it
   rejects a genuine match at index `0` and accepts the `-1` sentinel. Sites
   half-repaired as `if x.? and x >= 0:` still drop index-0 matches.
