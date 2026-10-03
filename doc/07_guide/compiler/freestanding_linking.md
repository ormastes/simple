# Explicit freestanding linking

Use `compiler.backend.linker.linker_wrapper.link_freestanding_to_native_v1`
when the caller supplies the entry point and needs a static image without CRT
discovery or an external-linker fallback. Pass object paths, archive paths, the
output path and a `NativeFreestandingLinkConfig`:

| Field | Meaning |
|---|---|
| `format` | `NativeFreestandingFormat.Elf` or `.MachO` |
| `target` | `RelocArch.X86_64`, `.AArch64`, or ELF-only `.Riscv64` |
| `entry` | Required exact entry symbol, usually `_start` |
| `output_byte_limit` | Maximum published artifact bytes; Mach-O requires at least 32768 |
| `executable` | Apply executable permissions to the staged image on Unix |

Success returns the requested path and actual `internal:elf` or
`internal:macho` engine identity. A link/size error leaves an existing output
unchanged. The caller owns the output directory; normalized lexical aliases of
an input reject. The fast path keeps resident arrays, so the byte limit does not
bound memory use. Bounded execution remains a separate unsupported contract.

ELF output is static ET_EXEC. Mach-O output is a fixed-address LC_UNIXTHREAD
image, not a dyld-linked application. Hosted macOS imports, TLS/unwind and signing
remain unfinished. RV64 dynamic/PIE/TLS and RV32 ELF output are unsupported.
Native target execution and production qualification are not established by
portable image construction. The checked dylib reader supplies metadata only.

For hosted FreeBSD, use the existing native wrapper with explicit internal
selection on a matching FreeBSD host. It selects FreeBSD CRT/libc/loader inputs,
preserves ABI notes, and brands/reseals the image. Its execution acceptance spec
remains unrun; source support is not a certified release claim.

Executable acceptance authorities are `item4_freestanding_adapter_spec.spl`,
`item4_linker_macho_spec.spl`, `item4_riscv_static_link_acceptance_spec.spl` and
the two `item4_freebsd_*_spec.spl` files under
`test/03_system/app/compiler/feature/`. Qualified Simple execution and canonical
manual generation are currently blocked by the missing admitted runtime.
