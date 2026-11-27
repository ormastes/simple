# Windows seed native linking loses the target ABI

Status: link-owner regression verified; rebuilt seed and full bootstrap qualification remain pending.

The release Phase 1 seed from `0bc9c4034d2a` (SHA-256
`6562f5bbcef6ad145d23b79be3d11cdb883487a2ab8cf380f73f2e21743b4e8c`)
failed `compile test/fixtures/bootstrap/native_hello_world/main.spl --native
--backend=cranelift --linker=lld` on Windows. GNU options reached `lld-link`;
the supported GNU ld alternative instead reported `cannot find -lc`.

`LinkerBuilder` retained its target for detection but dropped it at execution.
`NativeLinker::link` consequently selected its host command, while flags followed
the requested GNU ABI. Windows also requires the `.exe` suffix when spawning
`ld.lld` through Rust's process API. Both standalone-library selectors incorrectly
requested Unix libc on Windows.

The repair carries the target into execution, selects GNU PE emulation and
dynamic-base ASLR flags, uses MSVC flags for an explicit MSVC target, and removes
the nonexistent Windows `c` library. GNU PE's unsupported
`--unresolved-symbols=ignore-all` policy fails explicitly rather than silently
relaxing unresolved-symbol checks. Unix libc remains selected on Unix targets.

Validation used the actual production target, linker builder, linker and error
modules in an isolated Rust harness. The explicit-target regression compiled
real COFF/ELF objects, linked GNU PE and MSVC PE executables, executed both and
checked exact `Hello, World!` output plus exit code 37, and checked the ELF
artifact header. The unsupported-policy, target-command and Windows-library
regressions also passed. No stub runtime or replacement linker implementation
was used. The native regression is executable in the normal compiler suite via
`cargo test -p simple-compiler --lib test_explicit_target_links_real_pe_and_elf_artifacts -- --ignored`;
it requires Clang, LLD and a MinGW kernel32 import archive. Set
`SIMPLE_LINKER_TEST_CLANG` to the selected Clang executable.

Retained local evidence is under
`D:/dev/simple-user-storage/build/release-bootstrap-20261123/phase1-cranelift-hello`
and `target-linker-harness`. Native-build driver diagnostics separately hit a
2 GiB RSS cap and a 180-second timeout; those do not establish compiler failure
or Hello success. The still-running whole-suite collection and any newly built
seed require their own receipts.
