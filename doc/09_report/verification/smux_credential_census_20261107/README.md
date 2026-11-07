# Private credential native census repair

PR #7770's post-merge Required Gates run 42375503274 failed with six stale
C-only policy entries: the exported definitions lived in a header excluded
from the implementation census. The declarations and implementation macro
remain in that header; the unchanged implementation body now lives in its
included `.c` file. No policy entry, baseline or scanner was changed.

Source checkpoint: `8e0bcf257a95d2cc11fab7bc3672daf9a9fed0f6`.
The extracted body is byte-identical to the original header body. Both runtime
and native fixture still include the same header with the same macro.
Historical native evidence remains tied to its original source SHA; no new
native, Simple or full-runtime qualification is claimed.

One targeted command passed (CPUs 0–4):

```
sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev HEAD --baseline-rev d1739a85272ad13c50b45e8e00d2d18dab27eb4a
```

The attached log records 15 selftest fixtures and zero new single-lane symbols.
This verifies the source census fix, not full runtime linkage or orchestration.
