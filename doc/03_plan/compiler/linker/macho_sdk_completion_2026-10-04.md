# Mach-O SDK provider completion

The user requires a runnable, explicitly selected Simple linker on all five
hosts. macOS SDK support is an implementation obligation within that goal; a
typed seam or a parser accepting one small fixture is not a substitute for it.
Design authority: `doc/05_design/compiler/linker/macho_sdk_providers_2026-10-04.md`.

| Stage | Required implementation | Acceptance and current state |
|---|---|---|
| Shared provider metadata | Address-free typed providers used by actual hosted fixups/image construction; binary inputs retain their original validation before projection | Source implemented and independently reviewed; eight authored scenarios cover both architectures, binding/TLV bytes, malformed binary/metadata refusal, absent versions and explicit unsupported access policies; execution UNRUN |
| Both SDK text formats | Strict tagged/multi-document v4 YAML and v5 JSON readers with target selection, schema/default semantics and resource bounds | Source implemented: independent LLVM TextAPI fixtures and nine authored scenarios cover target/default semantics, metadata retention, malformed inputs, logical quotas, actual leaf/TLV image flow and file-route output preservation; all Simple execution UNRUN. See text-stub reader design for explicit accepted/rejected syntax; broad SDK compatibility remains unverified |
| Dependency and access rules | Inline/external reexport closure with exact identities, bounded cycles, aliases and root binding ordinals; actual client/umbrella enforcement and explicit SDK/search ownership | Graph, direct-client policy and native SDK/search source implemented; owner-specific dependency @rpath source candidate now retains binary/V5 metadata and routes real native lookup through owner context. Acceptance covers real transitive imports and aliases without promoting leaf loads; runpath candidate assertions cover real files and malformed-input output preservation. All execution remains UNRUN. Final candidate review, broad SDK compatibility, legacy reexport commands and remaining policy semantics stay open; this row is not qualified complete |
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
Exact core `78194e42070`, native routing `ccb9ae0c20b` and seven-case acceptance
`f64c60b4f56` received independent source review without concrete P0/P1 findings;
this closes that candidate review, not the row's execution or SDK qualification.

Managed internal-engine admission, bounded/no-swap worker evidence and Windows,
Linux, FreeBSD and SimpleOS execution remain separate requirements. External
hosted defaults remain unchanged. All Simple runtime/host gates are UNRUN until
an admitted deployed runtime and actual host evidence are available.
