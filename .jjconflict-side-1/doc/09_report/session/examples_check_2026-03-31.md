# Examples Check 2026-03-31

**Date:** 2026-03-31  
**Scope:** Current `examples/` verification against `bin/simple` in the working tree  
**Method:** `bin/simple <file>` for report-advertised sample commands, then folder-by-folder `bin/simple compile <file> -o /tmp/example-check.smf` with `timeout`

## Summary

The current `examples/` tree does **not** match the stability claims in
`doc/09_report/2026/02/examples_reorganization_complete_2026-02-16.md`.

The February report says learning examples `01-11` are "stable, documented,
ready to use". The current tree shows a different state:

- some examples still run correctly
- many examples fail with parser or semantic errors
- several examples hang or take long enough to hit the timeout budget
- the sampled failures look more like API/parser drift plus module issues than a
  single native-process crash

## Reported Sample Commands Rechecked

The February report includes this verification block:

```bash
bin/simple run examples/01_getting_started/hello_native.spl
bin/simple run examples/02_language_features/blocks/custom_blocks.spl
bin/simple run examples/03_concurrency/async_basics.spl
bin/simple run examples/07_ml/pure_nn/01_basics/xor_minimal.spl
```

Current results:

| Example | Result | Notes |
| --- | --- | --- |
| `examples/01_getting_started/hello_native.spl` | PASS | prints `Hello World` |
| `examples/02_language_features/blocks/custom_blocks.spl` | FAIL | parse error: `function arguments: expected Comma, found RBrace` |
| `examples/03_concurrency/async_basics.spl` | TIMEOUT | did not complete within 12s |
| `examples/07_ml/pure_nn/01_basics/xor_minimal.spl` | PASS | completed and printed XOR forward-pass output |

This means the report's own verification sample no longer holds for the current checkout.

## Folder-By-Folder First Failure

These are the first failing files encountered in a folder sweep. This is not a
complete list of every broken example; it is the first blocker per folder.

| Folder | First failing file | Result |
| --- | --- | --- |
| `examples/01_getting_started` | none observed | PASS in sampled run |
| `examples/02_language_features` | `examples/02_language_features/blocks/custom_blocks.spl` | parse error |
| `examples/03_concurrency` | `examples/03_concurrency/async_basics.spl` | timeout |
| `examples/04_data_formats` | `examples/04_data_formats/cbor_encoding.spl` | timeout |
| `examples/05_stdlib` | `examples/05_stdlib/platform_library.spl` | timeout with repeated `undefined symbol` export warnings from `nogc_sync_mut.platform` |
| `examples/06_io` | `examples/06_io/file/file_staging_parallel.spl` | parse error |
| `examples/07_ml` | `examples/07_ml/pure_nn/01_basics/autograd.spl` | parse error |
| `examples/08_gpu` | `examples/08_gpu/cuda/basic.spl` | semantic error: unknown extern `rt_cuda_available` |
| `examples/09_embedded` | `examples/09_embedded/baremetal/baremetal/blinky_stm32f4.spl` | parse error |
| `examples/10_tooling` | `examples/10_tooling/backends/backend_switching.spl` | parse error |
| `examples/11_advanced` | `examples/11_advanced/mir/mir_json.spl` | semantic error: undefined identifier `MirConstValue` |
| `examples/ui` | `examples/ui/demo_async.spl` | timeout |

## Additional Failures Observed Early

- `examples/03_concurrency/async_basics_alt.spl`
  - semantic error: unsupported path call `["Future", "ready"]`
- `examples/03_concurrency/async_structure.spl`
  - parse error inside imported async library source
- `examples/03_concurrency/concurrency_modes.spl`
  - parse error
- `examples/02_language_features/blocks/user_defined_blocks.spl`
  - timeout
- `examples/02_language_features/execution_context.spl`
  - parse error
- `examples/02_language_features/syntax/attribute_syntax.spl`
  - parse error
- `examples/02_language_features/syntax/spawn_syntax.spl`
  - parse error

## Interpretation

Current failures cluster into four categories:

1. Parser drift
- many example files use syntax no longer accepted by the current parser

2. Semantic/API drift
- examples reference symbols or call patterns that no longer exist or are no
  longer supported

3. Import/module regressions
- some examples stall while loading modules and emit unresolved export warnings

4. Long-running or hanging examples
- several examples do not finish inside the timeout budget, especially async/UI
  and some stdlib/data-format paths

## Conclusion

The current `examples/` problem is broader than one crashing file. The more
accurate statement is:

- no native signal-based crash was confirmed in the sampled sweep
- the current tree has multiple broken folders
- the February reorganization report is stale relative to the present checkout
- the first user-visible break in the report's own advertised validation sample
  is `examples/02_language_features/blocks/custom_blocks.spl`
- the first hang in that sample is `examples/03_concurrency/async_basics.spl`
