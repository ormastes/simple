# Coverage-aware parser ownership constraints

- Preserve the existing qualification cap of **8,388,608 KiB tree RSS** and
  its managed time budget. The small native fixture does not prove this cap.
- Measure the corrected whole-source workload under the same owner boundary.
  Retain peak RSS, elapsed time, producer/source identities, actual source and
  object counts, terminal status and linked Hello World evidence.
- SSpec fixture compilation has a 1,200,000 ms deadline and 8 MiB captured
  output bound; each native mode has a 120,000 ms deadline and 1 MiB output
  bound. Use the outer campaign resource supervisor for process-tree RSS.
- Run compilation once and each policy once per SSpec process. Missing
  canonical producer admission, compilation failure, timeout or nonzero
  native exit fails; none becomes a skip or successful non-execution.
- Promotion currently walks accumulated coverage containers per source.
  Record its actual elapsed-time cost; correctness alone is not a memory or
  performance admission result.
