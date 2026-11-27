# LLD defsym canonical trigger diagnostic — 2026-11-03

Reviewed release source `a41511004a0`. No code/DB changes; no claim, compiler build, Simple compilation, heavy test, native execution or QEMU run.

## Result

The linker-expression hazard exists for a manually supplied hyphenated ELF symbol, but the historical **workspace/source-path hyphen trigger is not established in current canonical compilation**. Do not reopen the historical record as a reproduced current defect, and do not patch source merely from the raw interpolation.

Both producer owners now sanitize path punctuation:

- Pure Simple `src/compiler/00.common/module_path_naming.spl:230-271` starts with `module_source_relative_path`, strips known prefixes/extensions, permits ASCII alphanumeric/underscore/dot/slash, and replaces everything else (including hyphen) with underscore. `driver_entry_closure_core.spl:237` delegates to this owner. Existing `test/01_unit/compiler/common/module_path_naming_spec.spl:71` explicitly expects `/tmp/probe-dir/entry.spl` -> `.tmp.probe_dir.entry`.
- Rust bootstrap `src/compiler_rust/compiler/src/codegen/common_backend.rs:3092-3146` strips source_root and sanitizes each path component to ASCII alphanumeric/underscore/dot before joining with `__`. `pipeline/native_project/compiler.rs:810,964-974` passes that prefix into MIR mangling; `mangle.rs:395` composes prefix and function with `__`. Thus even a correctly rooted `probe-dir/entry.spl` yields the safe `probe_dir__entry__spl_start` shape.
- Blame for both sanitation bodies reaches `ae55a7467197` (restoration history); this is **not** independently identified original repair provenance or native proof.

`simpleos_native_symbols.spl:159` still returns nm-discovered symbols and `simpleos_native_linkers.spl:100,107,539` still interpolates raw defsym RHS. The shell UP2 owner `scripts/os/build-simpleos-up-squared-apollo-lake.shs:109-116` first requires an exact constant safe symbol, so it does not admit the hyphen control. A custom exported name might be a separate contract investigation, but it does not reproduce the reported canonical source-path issue.

## Real bounded ARM64 object/link probe

Installed `/home/yoon/dev/llvm/install/bin/clang --target=aarch64-none-elf -c` assembled one return instruction per fixture into real ARM64 ELF objects. Actual `ld.lld -m aarch64elf -e spl_start --defsym=...` results:

| Fixture | Result |
|---|---|
| Canonical-derived `probe_dir__entry__spl_start`, unquoted RHS | exit 0; llvm-nm proves alias and original equal address |
| Manually hyphenated `probe-dir__entry__spl_start`, unquoted RHS | exit 1; symbol-not-found diagnostics split expression into `probe` and `dir__entry__spl_start` |
| Same manually hyphenated symbol, literal quoted RHS | exit 0; llvm-nm proves alias and original equal address |

Evidence directory: `/tmp/parallel-three-tracks-20261103/bugs/lld-defsym-probe/` contains assembly, objects, linked files, exact argv/status logs, nm outputs and results.txt. These are hand-authored assembly fixtures selected from source-derived naming, **not** artifacts emitted by executing Simple. No actual user-program recurrence has been shown. Preserve historical closed status with this diagnostic annotation rather than claiming new native acceptance or requiring an unjustified production change.
