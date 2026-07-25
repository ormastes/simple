# Core-C native paths could not resolve `text.strip`

- **Status:** pure-Simple dispatch fixed; fresh runtime regression pending
- **Observed:** the strict pure-Simple lint binary accepted a clean file, then crashed with `function not found: str.strip` on a deny fixture.
- **Cause:** `strip()` is a documented public alias implemented by the Rust interpreter and stdlib, but pure-Simple interpreter, C generation, and MIR native lowering only dispatched `trim()`.
- **Fix:** route both public spellings through the same existing trim implementation in all pure-Simple interpreter/codegen owners.
- **Regression:** existing language contracts require `"  hello  ".strip() == "hello"`; bootstrap essential-tool smoke now drives the former crash branch with `T001` plus `STUB003`. The next fresh lint shard must exit 1 rather than crash; this session reached the lint lane's three-cycle cap, so that execution is intentionally deferred.
