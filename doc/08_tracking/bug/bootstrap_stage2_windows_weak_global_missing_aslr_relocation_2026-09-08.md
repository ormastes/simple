# Stage 2 Windows globals keep preferred-image pointers after ASLR

Status: root cause reproduced and compiler fix verified by a focused source regression; fresh producer build and canonical Stage 2 admission pending.

The preserved candidate `build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe.rejected`
(SHA-256 `3e68d8d94ff78bcdaa41ae264cd6f290f9037791215d0a05316434eff2d8c456`)
fails before CLI dispatch. `--version` exits `0xC0000005` without output.

GDB stops at `__module_init_app__cli__native_build_warm_receipt+37`, instruction
`mov %rax,(%r8)`. `r8` is `0x1428c88d0`, the preferred-image address of
`app__cli__native_build_warm_receipt__NATIVE_BUILD_WARM_CANDIDATE_ENV`; the
actual image base for that launch is `0x7ff71daf0000`.
The caller is `__simple_call_module_inits`, reached from `main`.
The initialization stores a newly allocated text value through an invalid
global address. The module's Simple source declaration is valid.

## Cause

The rejected PE has preferred image base `0x140000000`, enables `DYNAMIC_BASE`,
and contains a base relocation directory. Nevertheless its `.refptr` slots
at RVAs `0x26bdb28`, `0x26bdb30`, and `0x26bdb40` have no `DIR64` records.
These slots reference the three warm-receipt globals. Neighboring function
and literal reference slots do have `DIR64` records.

The preserved cached provider object is
`build/bootstrap/stage3/x86_64-pc-windows-gnu/stage2-native-cache/scope-4a4a35170c4e5ca6/objects/fd50d03df11722cd.o`.
It contains `IMAGE_REL_AMD64_ADDR64` references to the globals, but defines
the globals with COFF storage class 105 (`WEAK_EXTERNAL`), positive storage
sections, and no auxiliary records. GNU linking resolves their preferred
addresses without creating the necessary loader relocations.

The owning bootstrap producer is
`src/compiler_rust/compiler/src/codegen/common_backend.rs::declare_globals`,
which selected `Linkage::Preemptible` for every local global. The correction
selects `Linkage::Export` for Windows definitions. Imports still use
`Linkage::Import`; non-Windows definitions retain their existing linkage.
This is a bootstrap-producer correction, not a replacement of pure-Simple
tooling with the Rust seed. No runtime or application workaround is used.

## Falsifiable evidence

The two-file Simple fixture in
`test/fixtures/bootstrap_windows_global_relocation` initializes/imports a text
global and mutates a numeric module global. A strict build with the admitted
Phase 1 producer compiled both files successfully, but its executable exited
`-1073741819` (`0xC0000005`).

An isolated diagnostic copied the emitted objects and changed only the two
defined data symbols' storage class from 105 to 2 (`EXTERNAL`). It preserved
their code, data, symbol names, and relocation records. Relinking those copies
produced exit 0 and the exact `bootstrap-global-relocation: pass` marker.
Neither the diagnostic executable nor patched objects are admissible compiler
or deployment artifacts.

Direct PE inspection also proves the fix's mechanism: the original fixture's
provider `.refptr` slots at RVAs `0x8e3cc0` (counter) and `0x8e3cd8` (text)
have no `DIR64` records; both records exist after relinking the strong-symbol
copies. The consuming module's imported text reference is relocated in both
images, isolating the defect to references to the owner's weak definitions.

Evidence is retained in `build/native_probe/astra_stage2_crash/`:

- `gdb-version.txt`: actual rejected candidate's registers, stack, and instruction.
- `pe-headers.txt`, `pe-symbols.txt`: candidate image metadata and symbols.
- `globals-before.json`: native Simple fixture's failing exit status.
- `strong-diagnostic.json`: original object hashes, changed symbols, exact link arguments, and passing output.
- `global-base-relocations.json`: before/after loader-relocation records for every fixture global pointer.
- `diagnostic_link.py`: reproducible isolated symbol-class experiment.

The new integration target `src/compiler_rust/compiler/tests/coff_module_globals.rs`
contains `coff_module_globals_have_relocatable_owner_definitions`, which emits Windows
and Linux objects and checks data definitions, ensuring the original weak
COFF representation fails while preserving ELF behavior. The source regression
passed against the rebuilt current compiler library: `1 passed; 0 failed`,
with both target objects checked in that test. The first `--lib`
attempt could not build because the existing test at
`compiler/src/interpreter_extern/mod.rs:3295` calls nonexistent `Value::as_array`
(`E0599`); the focused regression therefore uses a standalone integration
target through the public Codegen API.
`scripts/check/check-bootstrap-windows-global-relocation.shs` is the native
fixture gate; its default compiler remains `bin/simple`.

The passing source-test log is `object-integration-regression.log` (exit 0),
produced in a separate Cargo target by `run_object_regression.py` in the
evidence directory. The earlier internal-test build failure remains recorded
in `object-regression.log` and is not a compiler-wide test pass.

## Resume

Rebuild the bootstrap producer through the existing authority wrapper, then
let it regenerate Stage 2. The producer source change must invalidate its
old fingerprint and the corresponding object cache; retain the old cache and
rejected candidate as evidence instead of modifying them.

```sh
SIMPLE_NO_STUB_FALLBACK=1 BOOTSTRAP_STAGE3_FINGERPRINT_TRACE=1 \
sh scripts/bootstrap/bootstrap-windows.sh --full-bootstrap \
  --stop-after-stage2 --backend=cranelift --no-mcp --verbose --output=build/bootstrap
```

The scheduler should run the object regression and focused native fixture
against the new producer before accepting the fresh Stage 2 sanity result.
