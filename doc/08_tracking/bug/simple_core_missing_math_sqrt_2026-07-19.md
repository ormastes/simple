# Simple-core omitted the math square-root ABI

- **Status:** pure-Simple owner and archive regression added; Stage 4 duplicate-check runtime pending
- **Observed:** the strict duplicate-check entry could resolve its text and array helpers but still failed to link `rt_math_sqrt`.
- **Cause:** simple-core had no owner for the public math SFFI symbol even though hosted native links already retain the platform math library.
- **Fix:** `core_math.spl` now exports `rt_math_sqrt` and delegates to platform `sqrt`; no duplicate C or Rust provider was added.
- **Regression:** the simple-core archive smoke requires both `rt_math_sqrt` and the already-owned `rt_array_extend_i64` before admitting the archive.
