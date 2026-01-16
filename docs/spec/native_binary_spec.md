# native_binary_spec

*Source: `simple/std_lib/test/features/codegen/native_binary_spec.spl`*

---

Native Binary Compilation - Feature #101

Overview:
    Standalone native binary generation using mold/lld/ld linkers with 4KB
    page-aligned code layout for optimal startup performance. Produces self-contained
    ELF/PE executables that bundle the runtime and can run without the Simple runtime.

Syntax:
    simple compile app.spl --native -o app
    simple compile app.spl --native --linker mold -o app
    simple compile app.spl --native --target aarch64 -o app-arm64
    simple compile app.spl --native --layout-optimize -o app

Implementation:
    - Uses Cranelift for code generation
    - Supports multiple linkers (mold > lld > ld) with automatic detection
    - Implements 4KB page-aligned layout optimization with phases:
      - .text.startup: Process initialization
      - .text.first_frame: First UI render
      - .text: Hot path code
      - .text.cold: Rarely used code
    - Cross-compilation support for x86_64, aarch64, riscv64
    - Static linking of runtime functions
    - Symbol stripping and PIE support

Notes:
    - Produces standalone ELF/PE executables
    - Bundles runtime for self-contained execution
    - Supports 4KB page locality optimization
    - Layout phase annotation via #[layout(phase="...")] attribute
    - Cross-compilation to different targets
