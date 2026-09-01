# SQLite ACID native-store closure blocked

**Date:** 2026-08-25  
**Command:** `sh scripts/check/check-store-open-acid.shs`  
**Binary:** self-hosted release binary, 60,646,096 bytes  
**Status:** release-blocking verification failure

The focused SQLite provider stages completed successfully for both `:memory:`
and `/tmp/store_open_acid_probe/s1.db`: all eight A-D transaction stages
performed a visible insert and restored the prior row set after rollback.

The subsequent native enterprise-store stage failed during compilation:

```text
FAIL — native store link stage: error: semantic: cannot compile to standalone native binary: 14 function(s) contain constructs that require the interpreter
```

The check's temporary build log is intentionally removed by its trap, so this
run did not retain the 14-function list. Do not rerun the already-green SQLite
stages merely to recover it. The native compiler should retain the unsupported
closure list in a persistent diagnostic artifact, or the gate should copy that
list before cleanup.

## Impact

The transaction-control refactor has focused runtime evidence, but the complete
native enterprise-store acceptance criterion is not verified. SFFI admission
and signing must not treat this run as a pass.

## Required resolution

1. Make the native diagnostic identify and persist all 14 unsupported closure
   functions.
2. Remove or lower those interpreter-only constructs in Pure Simple.
3. Run the native-store stage once after the compiler/runtime fix.
