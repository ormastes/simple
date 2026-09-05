# Native I/O parity build cannot link `rt_file_mmap_read_text`

Status: LINKER FIXED; full parity rerun pending  
Observed: 2026-08-19, Linux x86_64

## Reproducer

```bash
bin/simple compile test/perf/io_parity/io_parity_simple.spl \
  --native --cpu native --opt-level aggressive \
  -o build/perf/io_parity/io_parity_simple
```

The current `bin/simple` identifies itself as the Rust bootstrap seed and exits
before producing the executable:

```text
error: codegen: undefined symbol: rt_file_mmap_read_text
```

The same extern is available to the interpreter and exists in the hosted Rust
runtime, but it is not admitted by this standalone native link surface. The I/O
parity runner intentionally does not fall back to interpretation, and removes
the previous receipt before compilation, so this state cannot produce PASS.

## Impact

Strict mmap parity requires consuming mapped bytes. Replacing this operation
with `rt_file_mmap_len` would restore compilation by measuring metadata rather
than mmap data and is therefore not an acceptable workaround. No C/Rust/Simple
benchmark row or retained PASS receipt was produced.

## Acceptance

- An admitted pure-Simple x86_64 compiler builds the reproducer without the
  Rust seed serving as the production engine.
- The resulting executable resolves `rt_file_mmap_read_text` without fallback.
- `run_io_parity_benchmarks.shs` emits byte-identical mmap checksums for C,
  Rust, and Simple and retains a `verdict=PASS` receipt with engine hashes.

## Root cause and repair (2026-08-19)

The canonical Simple declaration and both text-ABI lowering registries already
lowered `rt_file_mmap_read_text(path: text)` to the raw `(path_ptr, path_len)`
runtime ABI. The hosted runtime also exported that exact raw function. The
remaining gap was the in-process native relocation owner in
`src/compiler_rust/compiler/src/elf_utils.rs`: it admitted `rt_file_mmap_len`
and the boxed `_rv` mmap read variants, but omitted both raw mmap read exports.

The resolver now admits `rt_file_mmap_read_text` and the adjacent
`rt_file_mmap_read_bytes` symbol. Focused coverage checks the two resolver
entries and compiles/executes a standalone two-symbol mmap fixture with an
isolated cache. The exact I/O parity source now compiles natively with the
patched seed. The full parity benchmark was intentionally not rerun in this
repair lane, so the checksum/receipt acceptance item remains pending.
