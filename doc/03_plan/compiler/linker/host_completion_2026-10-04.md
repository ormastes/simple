# Simple linker host completion matrix

User requirement, 2026-10-04: the opt-in Simple linker must run on Windows,
Linux, SimpleOS, BSD (the existing FreeBSD lane), and macOS. This extends the
execution gate explicitly to the linker running on each host. Emitting that
host's file format elsewhere does not prove this requirement. None of the rows
below is marked complete by source-only tests. External hosted linker defaults
remain unchanged; Simple linking is selected explicitly.

| Host | Existing source path | Concrete implementation and execution gate |
|---|---|---|
| Windows | Native wrapper has internal COFF/PE routing and AMD64/ARM64 handling | Complete runtime/library imports, relocation and unwind corpus; run the actual linker and its produced application on each admitted Windows architecture; preserve explicit selection and no-clobber behavior |
| Linux | Explicit internal ELF hosted wrapper; retained x64 stream handles COMMON/GOT/COMDAT | Complete remaining ELF/TLS/unwind and full-product semantics, trusted opt-in CLI admission, actual link/load/run corpus and constrained worker evidence |
| FreeBSD | Hosted ELF wrapper selects FreeBSD CRT/runtime and brands the image | Run actual linker/compiler/application in FreeBSD, validate CRT/interpreter/ABI and failures; use the repository QEMU bootstrap/check entrypoint when exercising from Linux |
| macOS | Explicit internal native route consumes objects/archives and binary/text providers; v4/v5 parsing, reexport graphs, direct-client checks, explicit SDK lookup and owner-specific dependency @rpath are source-implemented and independently reviewed. Legacy selectors/subframework inference are the next source lane. All remain runtime-unverified | Complete and review legacy provider semantics; verify actual SDK corpus; complete remaining SDK policy/binding and dyld-cache provider support, configuration/TLS/TLV/unwind/weak semantics and managed admission; execute the actual wrapper and Darwin loader/signing checks on both architectures |
| SimpleOS | Explicit cross-target BootLayoutPlan path emits x64/arm64 images | Separately establish a linker executable running inside SimpleOS, its file/process/runtime owners, and on-guest link/load/run acceptance; host-side image generation and booting a generated image alone are insufficient |

Current production admission also requires review: managed native mode rejects
internal selection before platform dispatch. Do not remove that protection to
make a demo pass. Add independently admitted internal-engine/runtime authority
and configuration bindings, preserving external default selection and explicit
unsupported errors for missing capabilities.

Per-host acceptance must record host/architecture, admitted producer/runtime,
source and input identities, explicit engine receipt, full object/archive/runtime
closure, independently inspected output format and actual execution status/output.
Exercise missing library, duplicate and unresolved symbols, relocation overflow,
cancellation, scratch/output limits and unchanged existing destination. Qualify
startup, representative request/link latency and peak memory on realistic inputs.
A common portable spec may be reused, but every claimed row needs its own run.

The preparation/publication split and strict Mach-O file adapter are shared
implementation prerequisites. Neither attests worker authority or closes native
host execution gates. The Mach-O adapter requires explicit versions/signing
identity and rejects unsupported policy; its binary/text leaf-provider path does not imply a
normal SDK or full application links successfully. Simple compilation, host/guest
runs, coverage and full Phase 4 qualification remain UNRUN.

Runpath source review now covers core `78194e42070`, native routing `ccb9ae0c20b`
and seven authored acceptance scenarios at `f64c60b4f56`, without concrete P0/P1
findings. This review does not supply an admitted runtime or complete any host row.
