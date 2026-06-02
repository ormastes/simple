# BrowserSession Uint8Array Search Dispatch Gap

## Summary

`BrowserSession.eval_script` can execute `Uint8Array.prototype.fill` on a
browser-registered typed array, but script-level `indexOf` and `includes` calls
currently return miss results after the same filled slots are readable through
indexed access.

## Reproduction

```javascript
var b = new Uint8Array(5);
b.fill(4, 1, 4);
b[1] + ':' + b.indexOf(4) + ':' + b.includes(4)
```

Current observed result:

```text
4:-1:false
```

Expected bounded browser-compatible result:

```text
4:1:true
```

## Impact

This blocks claiming full browser-script `Uint8Array` search prototype parity in
the JS/WebEngine/WASM GUI hardening lane. Direct native host coverage exists for
bounded `fill`, `indexOf`, and `includes`; BrowserSession script dispatch still
needs a follow-up fix.
