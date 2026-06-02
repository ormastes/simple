# BrowserSession Uint8Array Search Dispatch Gap

Status: Resolved 2026-06-02.

## Summary

`BrowserSession.eval_script` can execute `Uint8Array.prototype.fill`,
`indexOf`, and `includes` on browser-registered typed arrays. The prior miss
was caused by the `Uint8Array#indexOf` helper comparing byte values through a
string-normalized nested match path that did not return from BrowserSession
script execution even when the indexed byte was visible.

## Reproduction

```javascript
var b = new Uint8Array(5);
b.fill(4, 1, 4);
b[1] + ':' + b.indexOf(4) + ':' + b.includes(4)
```

Previous observed result:

```text
4:-1:false
```

Current bounded browser-compatible result:

```text
4:1:true
```

The broader negative-start browser behavior is also covered:

```javascript
var b = new Uint8Array(5);
b.fill(260, 1, 4);
b[0] + ':' + b[1] + ':' + b[3] + ':' + b[4] + ':' +
    b.indexOf(4) + ':' + b.indexOf(4, 2) + ':' +
    b.indexOf(4, -2) + ':' + b.includes(4) + ':' + b.includes(5)
```

Current expected result:

```text
0:4:4:0:1:2:3:true:false
```

## Impact

This no longer blocks the bounded BrowserSession `Uint8Array` search prototype
coverage in the JS/WebEngine/WASM GUI hardening lane. Full typed-array prototype
parity remains broader follow-up work under the main GUI hardening plan.

## Verification

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl test/unit/lib/common/web/browser_session_wasm_host_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> `8/8`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> `107/107`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> `213/213`
