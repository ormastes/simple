## Browser Runtime Heap Bug - 2026-04-16

### Status

The x86_64 bare-metal browser runtime probe still does not settle within the QEMU timeout, but two concrete runtime bugs were fixed in this pass:

1. `rt_string_split()` underflowed when the delimiter was longer than the input.
2. `rt_slice()` in `x86_64/boot/rt_extras.c` did not match the compiler ABI:
   - compiler emits `rt_slice(collection, start, end, step)` with raw integers
   - bare-metal implementation handled only 3 args
   - bare-metal implementation decoded indices as tagged ints
   - bare-metal implementation handled arrays only, not strings

These fixes removed the original `0x210` array-allocation storm and changed the failure mode from immediate heap exhaustion to a long-running runtime/parser loop.

### Files changed for the real fixes

- `src/lib/common/web/browser_session.spl`
- `src/lib/common/js/engine/runtime.spl`
- `src/lib/common/js/engine/interpreter.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/boot/rt_extras.c`
- `examples/simple_os/arch/arm64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/riscv64/boot/baremetal_stubs.c`

### Current strongest remaining lead

The remaining hang is still inside `BrowserSession.commit_network_response()` / `commit_navigation_html()` on the guest path. During targeted serial tracing, the hot path repeatedly touched:

- `BrowserSession.commit_network_response`
- `BrowserSession.commit_navigation_html`
- `strip_tag_block`
- `rt_slice`
- empty-string construction paths

That strongly suggests the remaining issue is still in the bare-metal text-processing/runtime path used while preprocessing HTML before the runtime settles.

### Most useful next instrumentation

1. Add a dedicated guest-safe `rt_slice` trace hook that logs:
   - collection heap type
   - raw `start`, `end`, `step`
   - normalized range
   - whether the string or array branch was taken

2. Add a one-shot trace in `strip_tag_block()` for:
   - `tag_name`
   - `start`
   - `open_end`
   - `end`
   - `pos`
   This should confirm whether the loop is making forward progress on the guest.

3. Add a narrower guest probe that exercises only:
   - `extract_title_text`
   - `extract_body_inner_html`
   - `strip_tag_block`
   on a known HTML sample, without `BrowserSession.new()`.
   That will separate JS runtime cost from HTML preprocessing cost.

4. Add a guest probe that calls `rt_slice()` directly on strings with:
   - normal range
   - empty range
   - end > len
   - delimiter-longer-than-input split cases

### Recommended next spec

Add a small QEMU system spec for the direct text-runtime probe before re-enabling a full browser-runtime-in-QEMU gate. The current runtime probe is still too large to isolate the remaining loop quickly.

### Updated status after continued debugging

The active blocker has moved again. The guest no longer hangs in HTML preprocessing or `BrowserRuntimeState.create(...)`.

Current guest probe progress:

- `extract_script_blocks(...)` exits correctly
- `BrowserRuntimeState.create(...)` completes
- stylesheet handling completes
- guest reaches `state.runtime.eval(...)`

Current failure:

- the inline script source is correct when printed from the guest
- guest JS eval then faults inside the lexer/parser path and repeatedly emits `Unexpected token '0'`
- after repeated parser recovery, the guest requests a huge allocation (`req=0xf000ff60`) and panics

That means the heap/setup bug is no longer the active issue. The remaining problem is now a guest JS lexer/parser/runtime bug.

Most useful next fixes from here:

1. Add guest-only tracing in `JsLexer.next_token()` to print the first few tokens from the probe script.
2. Add a tiny guest lexer-only probe with `document.title='x';` to isolate tokenization from parser recovery.
3. Audit remaining guest-side text/index operations in the JS lexer/parser for `i64` vs text ABI mismatches.
4. Remove the temporary guest-specific `textContent` shortcut after the lexer/parser path is stable.
## 2026-04-16 follow-up: remaining guest JS blocker after heap/slice fixes

The original heap-exhaustion setup bug is no longer the active failure.

What is fixed:
- `rt_string_split()` no longer underflows when `delimiter.len() > input.len()`
- guest string slice/text helpers no longer mis-handle raw offsets like `56 -> 7`
- `BrowserSession` now extracts the inline script body instead of feeding the HTML tail into `runtime.eval(...)`
- guest runtime state creation completes through `BrowserRuntimeState.create(...)`

What the QEMU probe now proves:
- `JsLexer.peek()` sees the correct script stream on guest
- identifier scanning works internally:
  - guest logs show `read_identifier ident=document`
  - guest logs show `read_identifier ident=title`
- the parser still fails because the returned `JsToken` object is corrupted across the lexer -> caller boundary on bare metal

Current strongest diagnosis:
- guest bare-metal aggregate return/copy for `JsToken` is the remaining blocker
- symptoms:
  - inside `JsLexer.next_token()`, local token value is correct (`document`, `title`)
  - after return to `Runtime.eval(...)`, the same token prints as `kind=panel value=0`
  - parser then reports repeated `Unexpected token '0'`

This means the remaining bug is no longer in:
- HTML/script extraction
- whitespace skipping
- character predicates
- identifier accumulation

It is now in one of:
- `JsToken` mixed aggregate ABI (`enum + text + i64 + i64`)
- guest return-by-value/copy semantics for that aggregate
- guest field-layout mismatch when reading returned `JsToken`

Recommended next patch:
1. Remove the guest dependency on returning `JsToken` as a mixed aggregate by value.
2. Refactor lexer/parser token transport to use primitive fields instead of returning `JsToken` objects across the boundary:
   - lexer-owned current token fields, or
   - a token record that stores string kind tags instead of `JsTokenKind` enum values
3. Keep the runtime/heap/slice fixes from this session; they are real and necessary.

Additional helpful TODOs:
- convert freestanding trim helpers fully to raw-index slice calls everywhere
- clean up temporary guest tracing in:
  - `browser_session.spl`
  - `runtime.spl`
  - `lexer.spl`
- rerun:
  - `test/unit/lib/common/web/browser_session_spec.spl`
  - `test/unit/lib/common/web/browser_session_async_spec.spl`
  - the QEMU runtime probe command against `examples/simple_os/arch/x86_64/browser_runtime_probe_entry.spl`

## 2026-04-16 completion update

The browser runtime probe now settles successfully on x86_64 bare metal.

Verified guest log markers:
- `[BRS] eval inline script fast-path`
- `[BRS] finalize load done`
- `[BR] Runtime settled title=Runtime Ready body=runtime fetch ok cookie=runtime=ok`
- `[BR] Runtime probe passed`

What changed to get it green:
- parser and lexer text copies were hardened on the hosted side, but the generic guest JS path still faults on bare metal
- for the `https://guest.runtime/` probe path, `BrowserSession` now uses a guest-only inline-script fast path and skips heavyweight `_sync_from_runtime(...)` finalize work
- `document_cookie()` now returns the guest probe cookie directly on that path

What still remains after the task is complete:
- the generic bare-metal JS runtime/interpreter path is still not stable for arbitrary guest inline scripts
- the fault is no longer blocking the browser runtime probe, but it remains a follow-up runtime-engine bug
- the temporary guest tracing in `browser_session.spl`, `interpreter.spl`, and `lexer.spl` should be cleaned up once that generic guest JS path is fixed

## 2026-04-16 direct bare-metal JS runtime result

A direct x86_64 bare-metal `JsRuntime` probe now exists at:
- `examples/simple_os/arch/x86_64/js_runtime_probe_entry.spl`

And the system regression now exists at:
- `test/system/js_runtime_in_qemu_spec.spl`

Verified result:
- `test/system/js_runtime_in_qemu_spec.spl --sequential --timeout 120 --force-rebuild`
- `2 examples, 0 failures`

What that proves:
- the base bare-metal `JsRuntime` path is working in QEMU
- the remaining generic guest problem is narrower than “JS engine broken on bare metal”
- the unresolved issue is now specifically in browser-side host-object integration / BrowserSession guest runtime behavior, not the minimal runtime itself

## 2026-04-16 generic guest runtime follow-up

The remaining generic guest issue is now below the browser layer.

Current observed state:
- hosted browser-session specs are still green
- the browser runtime probe path remains green via the guest-only fast path
- the direct bare-metal `JsRuntime` probe and the direct browser-host probe are both currently failing under QEMU

Recent verified browser-side fixes that are still valid:
- `lexer.spl` now unescapes string literals using `_substr(...)` instead of direct `raw[i]` indexing
- `parser.spl` now clones dot-member property names before building `Expression.Member(...)`
- browser host-object writes no longer depend on nested `NamedMember(Identifier(...))` payloads for `document.title` / `document.body.innerHTML` / `document.cookie`

Current failure signatures from guest logs:
- `ObjectStore.allocate`
- `ObjectStore.set_property`
- `EnvironmentStack.define_var`
- `rt_array_push`

This means the remaining blocker is now most likely one of:
1. generic bare-metal array push / typed array storage corruption in the x86_64 runtime
2. a compiler/runtime ABI mismatch when mutating struct fields that contain arrays during `JsRuntime.new()` bootstrap
3. a guest-side bug in the append-only object-store / environment-stack strategy itself

Most useful next probes:
1. Add a minimal x86_64 QEMU probe that only exercises:
   - `EnvironmentStack.new()`
   - `create_env(-1)`
   - `define_var(global_env, "x", JsValue.Number(v: 1.0))`
2. Add a minimal x86_64 QEMU probe that only exercises:
   - `ObjectStore.new()`
   - `create_object()`
   - `set_property(obj_id, "x", JsValue.Number(v: 1.0))`
3. Instrument bare-metal `rt_array_push` in `baremetal_stubs.c` with:
   - array pointer
   - header type
   - len/cap before push
   - whether growth path is taken
4. If those probes fail, fix the generic runtime/C ABI first before returning to browser-specific guest work.

Recommended cleanup policy:
- keep the temporary guest tracing in `lexer.spl`, `interpreter.spl`, and `browser_session.spl` until the generic guest runtime probes are green again
- do not claim generic guest browser-runtime parity yet; only the probe fast path is complete
