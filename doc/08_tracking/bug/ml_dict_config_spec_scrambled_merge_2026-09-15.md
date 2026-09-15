# ml/dict_config_spec.spl is a scrambled merge (2026-09-15)

- File: `test/01_unit/lib/nogc_async_mut/ml/dict_config_spec.spl`
- Observed: parse error `Unexpected token: expected expression, found Indent`. The file
  interleaves two different spec generations: `describe "PyTorch Dict Configuration":`
  at column 0, followed by col-0 `# @req`/doc-path comment blocks, followed by `it`
  blocks at 8-space indent (dangling without their `context` lines), plus a local
  `enum DType` whose sibling users (tensor_spec et al.) live in other files. The
  `test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl` mirror has a DIFFERENT, clean
  structure (contexts intact, `enum Device` local), so no faithful source exists to
  restore definitions from mechanically.
- Unblock condition: manually reconstruct the intended test list (re-indent the orphaned
  `it` blocks under restored `context` wrappers or drop the interleaved comment blocks).
  Left RED rather than guessed at — restructuring blind would risk changing what is
  asserted.
