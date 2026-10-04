# Mach-O SDK provider completion

The user requires a runnable, explicitly selected Simple linker on all five
hosts. macOS SDK support is an implementation obligation within that goal; a
typed seam or a parser accepting one small fixture is not a substitute for it.
Design authority: `doc/05_design/compiler/linker/macho_sdk_providers_2026-10-04.md`.

| Stage | Required implementation | Acceptance and current state |
|---|---|---|
| Shared provider metadata | Address-free typed providers used by actual hosted fixups/image construction; binary inputs retain their original validation before projection | Source implemented and independently reviewed; eight authored scenarios cover both architectures, binding/TLV bytes, malformed binary/metadata refusal, absent versions and explicit unsupported access policies; execution UNRUN |
| Both SDK text formats | Strict tagged/multi-document v4 YAML and v5 JSON readers with target selection, schema/default semantics and resource bounds | Source implemented: independent LLVM TextAPI fixtures and nine authored scenarios cover target/default semantics, metadata retention, malformed inputs, logical quotas, actual leaf/TLV image flow and file-route output preservation; all Simple execution UNRUN. See text-stub reader design for explicit accepted/rejected syntax; broad SDK compatibility remains unverified |
| Dependency and access rules | Inline/external reexport closure with exact identities, bounded cycles, aliases and root binding ordinals; actual client/umbrella enforcement and explicit SDK/search ownership | Open: real transitive imports, duplicate/conflicting identities, missing targets/dependencies and access-denied output preservation; never flatten exports or invent extra direct loads |
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

Managed internal-engine admission, bounded/no-swap worker evidence and Windows,
Linux, FreeBSD and SimpleOS execution remain separate requirements. External
hosted defaults remain unchanged. All Simple runtime/host gates are UNRUN until
an admitted deployed runtime and actual host evidence are available.
