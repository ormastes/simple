# Mach-O SDK provider completion

The user requires a runnable, explicitly selected Simple linker on all five
hosts. macOS SDK support is an implementation obligation within that goal; a
typed seam or a parser accepting one small fixture is not a substitute for it.
Design authority: `doc/05_design/compiler/linker/macho_sdk_providers_2026-10-04.md`.

| Stage | Required implementation | Acceptance and current state |
|---|---|---|
| Shared provider metadata | Address-free typed providers used by actual hosted fixups/image construction; binary inputs retain their original validation before projection | Source implemented and independently reviewed; eight authored scenarios cover both architectures, binding/TLV bytes, malformed binary/metadata refusal, absent versions and explicit unsupported access policies; execution UNRUN |
| Both SDK text formats | Strict tagged/multi-document v4 YAML and v5 JSON readers with target selection, schema/default semantics and resource bounds | Source implemented: independent LLVM TextAPI fixtures and nine authored scenarios cover target/default semantics, metadata retention, malformed inputs, logical quotas, actual leaf/TLV image flow and file-route output preservation; all Simple execution UNRUN. See text-stub reader design for explicit accepted/rejected syntax; broad SDK compatibility remains unverified |
| Dependency and access rules | Inline/external reexport closure with exact identities, bounded cycles, aliases and root binding ordinals; actual client/umbrella enforcement and explicit SDK/search ownership | Graph, direct-client policy, native SDK/search and owner-specific dependency @rpath source are independently reviewed. Legacy selector and old-format subframework inference source is implemented/reviewed with nine main plus three modes authored real-file scenarios. All execution remains UNRUN. Dedicated alias/quota boundaries, broad SDK compatibility and other policy semantics stay open; this row is not qualified complete |
| SDK binding and qualification | Correct weak/TLV semantics, Objective-C export expansion and linker-directive handling, normal SDK discovery/integration and native Darwin qualification | Open: correct bind flags/ordinals, missing weak imports, real x64/ARM64 link/load/run/signing evidence plus full compiler/application corpus |

Existing strict JSON parsing can reject duplicate decoded keys and trailing data,
but requires explicit quotas at the owning boundary. Existing permissive YAML
parsing loses syntax needed by real SDK documents; silently normalizing malformed
or unsupported input is not acceptable. No format subset may be labeled complete
v4/v5 support without an explicit account of accepted and rejected syntax.

LLVM fixture tools are independent syntax/metadata evidence, not Simple execution
or SDK authority. Known differences in client-policy enforcement require primary
contract assertions instead of using an external linker as the sole oracle.
An absent SDK/minimum version remains absent where the format permits it; format
defaults must have a documented source. A signing identifier is not client identity.

The runpath profile follows Apple link-time owner paths, preserves the project's
explicit inline-catalog precedence, and does not borrow executable/ancestor
runpaths. Current LLVM command-line runtime-path fallback and dyld's inherited
runtime stack are distinct. See `macho_provider_rpaths_2026-10-04.md` in the linker
design directory for V2 compatibility, SDK rerooting and contextual cache rules.
The legacy continuation is specified in `macho_legacy_reexports_2026-10-04.md`:
all matching ordinary dependency edges, unmatched-selector no-op, exact
header-derived library stems, checked command strings, header suppression and
old-format-only subframework inference. It must not turn modern ordinary SDK
dependencies into an unconditional recursive discovery workload.
Legacy source review covers `89da96988ee`, hosted guards `c6dcb1f96bb` and
`f77ad587503`, nine main scenarios through `006e145c405`/manual `7052901d52d`,
and three modes scenarios/manual `9a4e14a9eb4`, without concrete P0/P1 findings.
All-matches, weak/lazy/upward command classes and matched/unmatched missing-file
cases now have authored assertions. Weak visibility uses a present provider;
absent weak dependencies, weak-import semantics and additional alias/quota
boundaries remain open. No execution or complete-SDK claim follows.
Exact core `78194e42070`, native routing `ccb9ae0c20b` and seven-case acceptance
`f64c60b4f56` received independent source review without concrete P0/P1 findings;
this closes that candidate review, not the row's execution or SDK qualification.

Managed internal-engine admission, bounded/no-swap worker evidence and Windows,
Linux, FreeBSD and SimpleOS execution remain separate requirements. External
hosted defaults remain unchanged. All Simple runtime/host gates are UNRUN until
an admitted deployed runtime and actual host evidence are available.

## Status 2026-10-25 (verified against origin/release/1.0.0)

Checked against `origin/release/1.0.0` source and `git log` on 2026-10-25.
Honest host scope: only the claims below that cite a commit carry execution
evidence, and that evidence is from the commit message, not re-run here.

| Area | State | Evidence |
|---|---|---|
| Internal ELF x64 linker links the full self-hosted CLI | PARTIAL (Linux x64 only) | `59126e2c285` (PR #4014, 2026-10-20): native-built internal linker linked the 2793-object cranelift CLI in 79 s; output ran `--version`, `-c 'print(1+1)'`, hello, same as ld.lld. Peak RSS 21.3 GB, far above the 6000000000-byte bounded target, so ITEM4-REQ-009 stays OPEN |
| Native-built linker driver | DONE (Linux) | PR #3984 (`9c0ddc8662e`); native output byte-identical to interpreted driver on hello/wide/153-module links per `59126e2c285` |
| COMDAT / weak instance dedup across non-LLVM backends | DONE (object-writer side) | PR #4603 (`cbe361c2497`, core `0bf2df39343`): ELF and Mach-O writers; PR #4575 module-scoped mono COMDAT instances (always on inside the opt-in `SIMPLE_FILE_WORKERS=1` file-worker lane since P-G3 #4598; the `SIMPLE_MONO_MODULE_SCOPED` flag no longer exists). Producer-side only; it is not a linker-host gate |
| Windows hosted link line (mswsock, llvm-mingw runtimes, single-owner GNU COFF runtime) | DONE (external-linker wrapper) | PR #4507 (`a45f49099eb`), #4487 (`e0837cb030e`), #4490 (`8bd0ec39b5d`). These fix the clang/lld link line; they do not execute the internal Simple COFF engine on Windows |
| Object-hash link receipt | OPEN (PR #4356 held, not merged) | Guard-side recognition only: `8c35ad4b536` |
| Mach-O | PARTIAL / in progress | Hosted Mach-O source + `macho_writer.spl` dedup exist; conditional Mach-O build is in progress, not landed; Darwin link/load/sign execution UNRUN |
| FreeBSD, SimpleOS on-guest linker, Windows internal engine, PE ARM64 | OPEN | No host execution evidence on this base |
| S7-I04-AC01..AC09 umbrella scenarios | OPEN | Still NOT_IMPLEMENTED bodies; the full-CLI link above is partial input to AC06 (Linux only) |

Superseded 2026-10-25: earlier text saying all Simple-linker execution is
UNRUN is no longer true for Linux x64 ELF — see `59126e2c285`. Every other
host row and the bounded-memory/performance gate remain as stated above.
