# Bootstrap Guide (2026-02-18)

This guide is the quick bootstrap reference for the current repository layout.

## Current Layout

- Core sources: `src/core/`
- Full compiler sources: `src/compiler/`
- Bootstrap scripts: `scripts/bootstrap/`

`src/compiler_core/` is retired. Bootstrap and docs should use `src/compiler/`.

## Bootstrap Pipeline

1. `seed` compiles Core Simple sources.
2. `core1` compiles core/full Simple sources.
3. `core2` verifies self-hosting for core.
4. `full1` compiles full compiler/app entry.
5. `full2` recompiles for reproducibility check.

See detailed pipeline: `doc/build/bootstrap_pipeline.md`.

## Shared Frontend Contract

Frontend logic is shared, not duplicated:

- Core frontend runner: `src/core/frontend.spl`
- Full frontend runner: `src/compiler/frontend.spl`

Core compiler/interpreter and full compiler paths must call these shared entrypoints.

## Seed/Core Conditional Compile

Seed and core now support source-level conditional directives:

- `#if <condition>`
- `#elif <condition>`
- `#else`
- `#endif`

Trailing `:` is also accepted (`#if linux:`, `#else:`), matching Simple block style.

Common conditions:

- OS: `win`, `windows`, `linux`, `macos`, `freebsd`
- CPU/arch: `x86_64`, `aarch64`, `riscv64`
- Key/value: `os=linux`, `arch=x86_64`, `cpu=arm64`

Override target detection during bootstrap with:

- `SIMPLE_TARGET_OS`
- `SIMPLE_TARGET_ARCH`
- `SIMPLE_TARGET_CPU`

Full compiler frontend also uses the same core conditional preprocessing path
(`src/compiler/frontend.spl` -> `core.parser.preprocess_conditionals`) so
`#if/#elif/#else/#endif` behavior is consistent across core and full runs.

## Quick Commands

Linux/macOS full bootstrap:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh
```

FreeBSD native bootstrap:

```bash
./scripts/bootstrap/bootstrap-from-scratch-freebsd.sh
```

Windows bootstrap:

```bat
scripts\bootstrap\bootstrap-from-scratch.bat
```

Multi-phase bootstrap:

```bash
bin/simple scripts/bootstrap/bootstrap-multiphase.spl
```

## Script Map

- `scripts/bootstrap/bootstrap-from-scratch.sh`: end-to-end bootstrap
- `scripts/bootstrap/bootstrap-from-scratch-freebsd.sh`: native FreeBSD flow
- `scripts/bootstrap/bootstrap-from-scratch.bat`: Windows flow
- `scripts/bootstrap/bootstrap-multiphase.spl`: multi-phase bootstrap runner
- `scripts/bootstrap/bootstrap-minimal.sh`: minimal bootstrap path
- `scripts/bootstrap/bootstrap-core-only.sh`: core-only path

## Expected Output

- Final binary: `bin/simple`
- Intermediate artifacts: `build/bootstrap/`

## Related Docs

- `doc/build/bootstrap_pipeline.md`
- `doc/build/multiphase_bootstrap.md`
- `doc/guide/freebsd_qemu_bootstrap.md`
