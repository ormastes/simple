# macOS Metal MSL Library Micro-Diagnostic Contract

This diagnostic isolates the production Engine2D MSL-to-library boundary
without entering rendering or window management.

## Direct library probe

The pure-Simple probe must:

1. Generate source with `_engine2d_msl()`, hash it with SHA-256, and pass that
   same text to `metal_sffi_compile_shader`.
2. Record Metal availability, initialization, device count, device creation,
   and library creation as structured fields.
3. Read a library-compiler failure only through the typed `metal_last_error`
   wrapper. That wrapper converts the runtime C pointer with
   `rt_cstring_to_text`; an untyped dynamic call is forbidden.
4. Replace line breaks and cap the emitted error at 1,024 bytes while retaining
   the original length and truncation status.
5. Destroy every created library and device.
6. Never create a command queue, pipeline, framebuffer, CPU fallback, surface,
   or window.

## Trusted, bounded checker

The checker must:

1. Admit only the canonical self-hosted compiler and Metal runtime providers
   whose paths and SHA-256 values are bound by the trusted macOS Metal build
   manifest. The compiler is selected from `build_compiler_abs_path`; no caller
   path override is allowed. Admission accepts only the producer-issued
   identity/source-kind pair for the current frozen Stage-3 compiler. The
   Stage-3 manifest is reverified through the canonical trusted-build producer.
2. Require an executable, non-symlinked compiler with the exact manifest hash,
   reject Rust seed/bootstrap-seed/debug identities, and require the canonical
   default runtime and C-runtime provider paths and hashes.
3. Require the exact Metal availability, initialization, device, library, and
   last-error provider symbols before building.
4. Link the diagnostic with `SIMPLE_NO_STUB_FALLBACK=1`.
5. Run native compilation and the diagnostic through the same bounded process
   facade. Each child owns a fresh process group; on deadline the whole group
   receives TERM then KILL. Each stdout/stderr stream retains at most a 4-KiB
   head and 4-KiB tail plus a fixed-format omission marker, and the FIFO drains
   have their own bounded deadline so a descendant-held writer cannot hang the
   checker.
6. Use dyld logging to prove the manifest-bound Metal provider was loaded.
7. Reject missing fields, a non-64-character source hash, any CPU fallback, or
   any window-system use. A successful exit additionally requires exactly:
   `status=pass`, initialized/available fields of `1`, positive device count,
   passing device/compiler/library statuses, both cleanup fields of `1`, and
   zero-length, untruncated typed error evidence.

The checker intentionally does not invoke the full live Metal/window harness.

The helper spec imports the diagnostic module and checks single-line error
sanitization without initializing Metal.
