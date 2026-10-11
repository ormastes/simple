# Phase 2 runner build crashes while reporting a cold HIR source mismatch

Status: diagnostic repair implemented; native verification pending. The underlying
`cold-hir-module-source-mismatch` rejection remains unresolved and enforced.

The C31 pure-Simple diagnostic compiler (`8028c24d93c43300ca53a0e5840d7b2f80d9babe3f217318e3ff0ee36894bf4e`,
source `67893d944a326512fd2c3102a9c72ace908f612f`) fails while compiling
`src/app/test_runner_new/main.spl` with LLVM, `--entry-closure`, `--low-memory`,
eight requested workers, and no `SIMPLE_BOOTSTRAP` shortcut. This compiler is
not a canonically admitted Stage 2 artifact.

The worker completed HIR lowering for 218 modules, printed the normal
enum-contract pass result, then died with SIGSEGV before MIR. The coordinator
returned 117. Peak process-tree RSS was 2,351,160 KiB under an enforced
6,835,937 KiB cap, so this was not an RSS rejection. No runner or executed test
result was produced.

GDB caught the actual failing worker at
`CompilerDriver.capture_cold_hir_typed_receipts_v1 + 8068` (`0x1269304`). The
instruction dereferenced a nil value (`x0 = 3`) returned by indexing
`self.ctx.hir_modules[0]`. This dictionary is keyed by module name, not a numeric
position. The faulty diagnostic ran after receipt capture had already returned
`cold-hir-module-source-mismatch`; it hid that rejection behind a crash.

The repair finds the first mismatched source using the retained module names,
checks dictionary membership before reading a module, and reports the source
index, snapshot root, expected source path, module name, and actual HIR path.
Each text field is bounded to 256 characters. The driver still records the
original receipt failure and returns false; no source-identity check is relaxed.

Regression examples in
`test/01_unit/compiler/cache/cold_hir_admitted_entry_seed_spec.spl` cover a
mismatch after a valid source, an absent named module in a nonempty map, and a
source outside the admitted root. These examples have not yet run: no qualified
full CLI or test runner is available. The next producer must expose the actual
path mismatch before that separate defect can be repaired.

Evidence retained outside the working tree:

- `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c31-producer-c31-runner/result.json`
- The same directory's `worker-stderr-full.log`, `per-pid-rss.tsv`, and
  `process-tree-rss.env`.
- The same directory's `gdb-attempt3/construction.log` contains the caught signal,
  failing worker stack, instructions, and registers. The earlier GDB setup stopped
  on a normal subprocess exit and is not crash evidence.

Source HEAD/tree, all selected physical source hashes, full index membership,
and compiler/runtime input hashes were checked before and after both attempts.
