# macOS Native-Link Configuration — Pure-Simple Ownership

Context: producing the deployable self-hosted macOS arm64 binary via the staged
`build bootstrap --backend=llvm-lib` pipeline surfaced a chain of macOS host-link
gaps (the shipped Jun-2026 binary was cargo-linked, so the native-build link path
was never exercised on macOS). The product-side fixes belong in **pure Simple**;
the items that could only be done in the Rust seed are recorded here as feature
requests with the reason pure Simple was not possible.

## Done in pure Simple

- FR-MACLINK-001: The macOS host-link flag set — libraries `z, ffi, edit, zstd,
  xml2, ncurses, objc, iconv`; frameworks `Metal, CoreGraphics`; search path
  `/opt/homebrew/lib` — shall be owned by the pure-Simple backend. **Done:**
  `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` `link_native_unix`
  macOS branch (+ `link_native_cc` bootstrap fallback), gated to `os == "macos"`.
- FR-MACLINK-002: The bootstrap seed-wrapper C shall emit Mach-O section syntax
  (`__DATA,__data`) on Apple targets, not ELF `.data`. **Done in pure Simple:**
  `src/app/cli/bootstrap_main.spl`, `src/compiler/80.driver/driver_bootstrap.spl`,
  `src/os/port/_BootstrapCross/cross_compile_stages.spl` (`__APPLE__`/`__MACH__` preprocessor
  branch).

## Could not be done in pure Simple — Rust seed only (feature requests)

The Rust seed (`src/compiler_rust/`) is the bootstrap-only compiler. Its
`native-build` has a stub-fallback symbol-classification pass
(`SIMPLE_NO_STUB_FALLBACK`) that the self-hosted Simple backend does **not** have
(the Simple linker resolves via `.lsm`/`.smf` archives + direct linking, with no
equivalent classification pass). The staged pipeline uses the seed for Stage 1/2,
so these seed paths had to be patched in Rust for the bootstrap to proceed. There
is no pure-Simple site that controls the seed's behaviour.

- FR-MACLINK-003: The seed `macos()` link config
  (`src/compiler_rust/common/src/platform/link_config.rs`) duplicates the libs/
  frameworks/search-path now owned by FR-MACLINK-001. *Reason pure Simple not
  possible:* it is the Rust seed's own link config; the seed is not generated
  from Simple. **Request:** derive the seed's macOS link flags from a shared
  source (or the Simple backend) so the two cannot drift and future macOS lib
  additions need no Rust edit.
- FR-MACLINK-004: The seed's macOS system-symbol suppression table
  (`pipeline/native_project/tools.rs` `is_macos_system_symbol`) had to be widened
  (libc/libm names + `ffi_/el_/history/xml/ZSTD_/MTL/Unwind_/dyld_/tlv_` families,
  `$`-ABI-suffix stripping). *Reason pure Simple not possible:* the suppression
  pass exists only in the seed's stub-fallback path. **Request:** either retire
  the seed stub-fallback in favour of the Simple linker's direct resolution for
  host builds, or port the classification to the Simple backend.
- FR-MACLINK-005: The seed's compiler-provided runtime-symbol exemption
  (`pipeline/native_project/stubs.rs`) matched only the 2-underscore C names and
  missed Mach-O's extra leading underscore (`___simple_runtime_init`,
  `___simple_runtime_shutdown`, `___simple_call_module_inits`); fixed with
  `is_compiler_provided_runtime_symbol`. *Reason pure Simple not possible:* same
  seed-only stub-fallback path as FR-MACLINK-004. **Request:** fold into
  FR-MACLINK-004's resolution.
