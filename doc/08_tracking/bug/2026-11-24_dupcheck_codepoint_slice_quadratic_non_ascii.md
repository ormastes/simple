# dupcheck: quadratic tokenize on non-ASCII sources (code-point `text[a:b]`)

- **Date:** 2026-11-24
- **Status:** workaround landed (SourceSlicer); language/runtime gap open
- **Area:** `src/compiler/90.tools/duplicate_check/tokenizer.spl`, `_Detector/interner_and_logging.spl`

## Symptom
Cosine mode with `--include-c` over flattened `src/runtime/*.c` (82 files, 3.2 MB):
140 s native / 288 s seed. ~118 s of the native run was the extract pass.
`src_runtime_runtime_process.c` (209 KB, 5 non-ASCII lines) tokenized in 8.9 s;
the 47 KB all-ASCII `runtime_pool.c` took 12 ms.

## Root cause
`text.len()` and `text[a:b]` count code points. On a text containing any
non-ASCII byte both walk from the start (measured ~270 us per slice of a
200 KB text, vs O(1) for ASCII). The tokenizer slices every token out of the
whole file source, and extraction slices every block snippet, so each
non-ASCII file is quadratic.

## Workaround (this change)
`SourceSlicer` cuts non-ASCII sources once into 4096-code-point chunks and
slices within a chunk; ASCII sources keep plain `source[a:b]`. It returns
exactly what `source[a:b]` returns (pinned by
`test/01_unit/app/duplicate_check/source_slicer_spec.spl`); the cosine report
on the corpus is byte-identical. Result: 16.6 s native, ~20 s seed.

## Open gaps
1. **Runtime/language:** no O(1) byte-range text slice. A `text.byte_slice(a, b)`
   (or an O(1) code-point index for non-ASCII text) would remove the need
   for SourceSlicer.
2. **Latent correctness bug (deliberately preserved):** the tokenizer walks
   `source.bytes()` with byte offsets but bounds the loop with the code-point
   `source.len()` and slices with code-point `source[a:b]`. After the first
   non-ASCII character in a file, token values are shifted (the progress log
   shows bogus buckets such as `SimpleTokenKind::Operator:e`), and the last
   few bytes of the file are never tokenized. Fixing this changes cosine
   output, so it needs its own change with a new oracle.
