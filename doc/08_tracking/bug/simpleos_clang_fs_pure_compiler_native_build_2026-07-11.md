# SimpleOS Clang filesystem proof blocked by pure compiler native-build

## Status

Open. The guest Clang with embedded LLD builds and statically relinks. A current
zero-weak pure-Simple compiler builds and boots the QEMU kernel, but the live
guest compile/link/execute proof is not yet complete.

## Evidence

- Cross LLVM/Clang/LLD rebuilt with `CLANG_SIMPLEOS_EMBED_LLD=ON`.
- `clang_static.shs` produced a 122,233,168-byte static ELF with `_start` and
  zero undefined symbols (SHA-256
  `f5bb5e75f5b8bc7abb25c7b0b8baf49aa817381799490b0b3a2ccb4d667aa22b`).
- Fresh pure full CLI exact interpreter smoke passed, but that binary contains
  766 weak closure stubs. Its first kernel build hit a historical `cs` parser
  collision; after renaming the local, `check` parsed the entry and native-build
  failed in HIR lowering with `field access on nil receiver`.
- The prior stable pure full CLI passed its prerequisite smoke but segfaulted
  while native-building the same current entry.
- Three live build attempts were consumed; none reached QEMU. Do not retry in
  this session.

## Root follow-up

The focused diagnostic shard localized the SIGILL to bootstrap MIR entry-module
extraction. `if val hir_module = _bootstrap_entry_hir_module` entered with a nil
payload; the owner now uses an explicit presence check plus typed `unwrap`, with
a source regression.

The cache-preserving bootstrap then exposed the next earlier stage2 error:
`MirLowering.local_is_float` was called by inferred-float Let lowering but did
not exist. The shared MIR predicate and regression now exist. A subsequent
dynload recovery completed stage2 and stage3 with zero weak or undefined
symbols. The capped full-CLI cycle then stopped during discovery because three
terminal operands in `access_cli_grammar.spl` were dedented out of multiline
concatenations. The minimal three-indent fix now passes the Rust bootstrap-seed
parser/run check; the preserved cache is ready for the next build turn.

Produce a full CLI from the preserved recovery cache whose entry closure has no
weak internal compiler stubs and add one native-build regression for
`examples/09_embedded/simple_os/arch/x86_64/fs_elf_exec_smoke_entry.spl`.
Then rerun `scripts/os/build_clang_disk.shs` once. Do not weaken the wrapper to
the Rust seed or reuse a stale kernel.

## Recovery update

The preserved cache now produces a stage2 pure compiler with zero uppercase
weak definitions (SHA-256
`a5bd7c9e8f6bd5cb133912cd1066599ccacddc4e74a9e025a6de00ef8878662f`).
It built the current filesystem-exec kernel successfully: 257 modules, 0
failures, 21,592 KiB, SHA-256
`d247013b1c07036350ed15b4b3d9b3f5e70a0b3d8a7066be489b5ad593897626`.

The full-CLI relink was rejected: the bootstrap script had explicitly enabled
missing-runtime weak stubs. Strict mode now replaces that opt-in and deletes
stale stage4 output before linking; it exposes real optional-runtime/entry
closure unresolved symbols instead of emitting a false-green CLI.

The Clang gate did not reach QEMU. Its interpreted FAT writer silently produced
no prefix, so the wrapper now native-builds the existing writer with the proven
compiler. Canonical array `.len()` fixes let that writer compile, but its first
execution segfaulted before writing the prefix. Three Clang-gate fix attempts
are consumed. Static disassembly localized the crash: the core-C
`rt_file_read_bytes` returned `spl_file_read`'s raw `char*`, while the compiler
ABI and Simple callers require a tagged byte-array value. The runtime owner now
constructs a length-bearing byte array from binary file data. The sibling
writer now also matches codegen's four-argument path/data ABI instead of
misreading `path_len` as a data pointer. C syntax passes, but the writer and
QEMU must wait for the next capped turn.

## Live QEMU update

The ABI and packed-byte fixes now create a valid FAT32 image. QEMU reads the
correct BPB/signature, streams `/FSEXEC.ELF` at its exact 122,233,168-byte size,
and validates the ELF64 entry. Execution still stops before ring 3 at a BMI2
`shlx` emitted in PMM even though the build requests `--cpu x86-64-v1`; the
stage2 driver warns that option is ignored. Enabling `qemu64,+bmi2` did not
change the retained trap. The three-attempt cap is reached; guest Clang
compile/link/execute remains unproved.

## CPU/PMM and streaming update

Both native-build entrypoints now forward `--cpu` through
`SIMPLE_NATIVE_CPU`. Fresh CPU-v1 kernels no longer fault on BMI2. Removing
Option aggregate transport from the raw PMM allocator then allowed the final
capped kernel (`7995a823...`) to initialize PMM/VMM and a real user address
space.

That run failed when PT_LOAD mapping rewound the FAT stream from the 64-KiB
header read to file offset 4096. The loader now copies ranges within that
already-buffered prefix from memory and reserves the stream for forward reads.
No further QEMU attempt is permitted this session. A focused source check was
terminated after 90 seconds without output; validate this patch and run one
fresh gate next session.
