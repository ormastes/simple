# StarFive build blocked by stale Stage 2 codegen-root table

Status: RESOLVED FOR STARFIVE / stale Stage 2 retained as diagnostic only

## Reproducer

`SIMPLE_NO_STUB_FALLBACK=1 scripts/os/build-simpleos-starfive-jh7110.shs`
selects the only locally available diagnostic Stage 2 compiler and aborts while
compiling `binary_io.spl`:

`missing runtime fn 'rt_struct_receiver_valid' in BinaryReader.remaining`

## Root cause boundary

Current source already lists `rt_struct_receiver_valid` in
`runtime_symbol_is_codegen_root()` in
`src/compiler_rust/compiler/src/codegen/common_backend.rs`. Codegen injects the
call, so it must be declared even when it is absent from source-level referenced
call names. The selected Stage 2 executable predates that source fix. The
deployed Stage 4 executable separately exits 139 during focused checking.

The StarFive closure must not be weakened to avoid `BinaryReader`, and the Rust
seed is not admissible target, SPipe, or release evidence. Resume only with a
provenance-admitted rebuilt self-hosted compiler containing the current
codegen-root table, then rerun the canonical StarFive build once.

## Acceptance

- admitted compiler path, stage, producer receipt, and SHA-256 are retained;
- the unchanged StarFive entry closure reaches ELF64 RISC-V link;
- receipt entry is `0x40200000` and binds the exact compiler/linker/image hashes;
- no seed or stub fallback participates.

## Resolution — 2026-08-16

The provenance-admitted pure-Simple Stage 3 compiler at
`build/bootstrap-stage23-sync-final/stage3/x86_64-unknown-linux-gnu/simple`
(SHA-256 `e22b0e1ffee06b7ff46bb69b9b51ff8e28aab851fbafe9ff05efe193fa708d35`)
built and linked the unchanged board closure. The final receipt binds that
compiler and its PASS provenance manifest to the ELF/linker/root hashes. The
Rust seed and stale Stage 2 compiler were not used for acceptance.
