# Item 5 platform admission acceptance criteria

Status: NOT_IMPLEMENTED. These are planned observable acceptance criteria, not executed evidence.

Scope: I5-03 and I5-05: target, architecture, ABI, dependency and policy admission; typed refusal parity.

Authority: the selected requirements in `doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md` and the existing I5-01 through I5-14 acceptance plan remain intact. This package does not certify the whole item, any host, or any release.

The matching SSpec contains explicit failing skeletons only. It intentionally has no implementation helpers, fake success or execution results. No runtime, compiler, verification or doc generation is requested for this scaffold.

| Criterion | Requirement | Setup | Action | Observable threshold | Status |
|---|---|---|---|---|---|
| I5-P01-AC01 | REQ-002 | A sealed provider and host manifest agree on target, architecture, ABI, dependency digests and policy generation; observe initialization and effect counters. | Demand one granted capability through the production admission and loader path. | One admitted identity and one initialization; payload returns its expected value; no initialization or effect occurs before admission. | NOT_IMPLEMENTED |
| I5-P01-AC02 | REQ-002 REQ-012 | Use an otherwise compatible provider whose manifest names a different target operating system or object format. | Demand its capability with the host target unchanged. | Typed target incompatibility; zero provider initializations, payload calls and effects. | NOT_IMPLEMENTED |
| I5-P01-AC03 | REQ-002 REQ-012 | Keep target and policy valid; provider architecture differs from the host architecture. | Demand the capability through the production admission path. | Typed architecture incompatibility; zero provider initializations, payload calls and effects. | NOT_IMPLEMENTED |
| I5-P01-AC04 | REQ-002 REQ-012 | Keep artifact, target and architecture valid; change one word of the expected interface ABI digest. | Demand the capability using the incompatible locked ABI. | Typed ABI incompatibility; zero published callable permits, provider initializations and effects. | NOT_IMPLEMENTED |
| I5-P01-AC05 | REQ-002 REQ-012 | Prepare one provider with an omitted required dependency and another with a wrong dependency interface digest. | Demand each independently against the unchanged admitted dependency manifest. | Each produces the corresponding typed dependency refusal; zero provider initializations and unrelated dependency activations. | NOT_IMPLEMENTED |
| I5-P01-AC06 | REQ-002 REQ-012 | Prepare a compatible provider requiring a capability absent from the host grant. | Demand the denied capability without changing its required capability bits. | Typed capability or policy refusal; zero provider initialization and effects; no silent privilege expansion. | NOT_IMPLEMENTED |
| I5-P01-AC07 | REQ-002 REQ-012 | Admit a provider under policy generation A; publish generation B revoking its capability before a subsequent demand. | Demand the capability using the cached generation A admission. | Stale authority is rejected or revalidated against B and refused; zero new effects under the revoked authority; receipt identifies the evaluated generation. | NOT_IMPLEMENTED |
| I5-P01-AC08 | REQ-002 REQ-012 | Prepare one incompatible provider and record the corresponding unavailable capability error contract. | Perform the first demand, then repeat demand from a second caller against the same authority generation. | Both callers receive the same typed refusal contract; zero admitted receipts, initializations and effects; no substitution by a generic cached error. | NOT_IMPLEMENTED |

Executable skeleton: `test/03_system/runtime/provider/item5_pending/p01_platform_admission_spec.spl`.
