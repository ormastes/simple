# dataloader.spl doc example fails under --spl-doctest

- Found by: `test/03_system/app/test_runner/comment_kind_real_src_spec.spl`
  ("passes the example of the data loader library file"), left RED on purpose.
- Repro: `bin/simple test --no-session-daemon --spl-doctest src/lib/gc_async_mut/pure/data/dataloader.spl`
- Result: `FAIL ... (0 passed, 1 failed)`, `Line 22: error: semantic: cannot iterate over this type: Object { class: "DataLoaderIterator", ...}`
- Source: the example at `src/lib/gc_async_mut/pure/data/dataloader.spl:22`
  runs `for batch in loader.iter():` and the interpreter rejects the
  `DataLoaderIterator` object as not iterable.
- Unblock: make `DataLoaderIterator` iterable (or correct the documented
  example). Not a comment-doctest runner defect.
