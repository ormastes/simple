# Mach-O SDK provider closure acceptance

Twelve authored scenarios in `test/03_system/app/compiler/feature/item4_macho_closure_spec.spl`, tracing ITEM4-REQ-006. **Simple execution UNRUN**. This manual is authored, not generated execution evidence.

| Scenario | Independent assertion |
|---|---|
| Path normalization | Drive, UNC and POSIX roots survive normalization; traversal beyond absolute roots and drive-relative paths reject. |
| Relative provider files | Actual `@loader_path` and `@executable_path` reads select the staged stub and return its exact bytes/path; unsupported `@rpath` dependency rejects. |
| Flag grammar | Missing and repeated `-syslibroot`/`-client_name` singleton arguments reject during planning. |
| Graph limits | A valid real cyclic graph rejects insufficient source, byte, edge, symbol and cumulative work budgets; a shallow lookup limit rejects traversal. These are logical quotas, not process memory enforcement. |
| Duplicate identity | Repeated direct providers and conflicting declarations of one install name reject. |
| Native client identity | Matching signing identifier alone cannot grant access; actual `-client_name` permits the same real provider and object to produce a Mach-O image. Denial preserves the destination. |
| Unusable SDK provider | Missing leaf, mismatched install identity, wrong target and a reachable leaf requiring macOS 12 for a macOS 11 request refuse construction while preserving sentinel bytes. The deployment case checks the specific minimum-OS diagnostic. |
| Alias cycle and sibling | A genuinely binary-parsed alias branch cycles back to the root; lookup continues to a later inline defining sibling in both TBD formats. |
| Binary alias image | Both CPU fixtures preserve outward `_alias` and direct root ordinal1 in real emitted binding bytes while resolving the internal `_helper` name. |
| Whole-library cycle | Both formats find a reachable definition and terminate absent-symbol lookup without inventing an export. |
| Direct access policy | Explicit client, prefix direction and declared parent umbrella are checked against real restricted provider metadata. Generic parent-umbrella context is separate from native executable flag support. |
| Native transitive image | V4/v5 and x64/ARM64 root-inline-middle-external-leaf links emit exactly one direct dependency, original root install name/version, expected binding byte stream and rebased local pointer. A restricted indirect leaf remains accessible through the public root. |

Fixture provenance and external LLVM21.1.8 observations are recorded in `test/fixtures/linker/macho/RECIPE.md`. The mixed alias-cycle regression was added during source review; no executed RED/GREEN ordering is claimed. Alias fixtures are documented binary mutations, not LLD alias-generation or valid code-signing evidence.

An admitted self-hosted runtime is required for the pending command:

```
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_closure_spec.spl --mode=interpreter
```

These tests do not qualify Darwin loading, native execution, real SDK completeness, dynamic weak import behavior, signing validity, immutable file identity, bounded whole-process memory, or `@rpath` dependency search. Those remain separate product/runtime gates. No Rust seed, rebuild or runtime retry was used.
