# Caret unresolved local container intent V1

Status: **AUTHORED_NOT_RUN**. Authored companion to
`test/01_unit/app/llm_caret/cs_container_intent_v1_spec.spl`.
No compiler, tests, doc generation, native backend or production launch ran.

The pure adapter accepts an existing parsed `CsContainerRequest`, a host
executable, complete argv and a repository string. It returns unresolved
`CaretLocalContainerIntentV1` metadata. It does not produce
`LocalContainerRequestV1`, select an engine, translate host paths to guest
paths, mount anything or authorize execution. The local provider must
independently resolve its host-to-guest profile and revalidate every field.

| Requirement | Authored scenario and expected result |
|---|---|
| REQ-CARET-LOCAL-INTENT-001: exact unresolved values | Preserve empty/spaced/escaped/Unicode argv, a Windows host executable distinct from guest mount paths, repository, workspace and image. Copy each parsed mount source/target/read-only flag, ordered environment entries with embedded equals and empty values, and network. |
| REQ-CARET-LOCAL-INTENT-002: explicit refusal | Refuse real parser errors and absent container image; reject empty/NUL host executable or repository and NUL argv. Relative host identities remain unresolved metadata. |
| REQ-CARET-LOCAL-INTENT-003: bounded construction | Bound every copied text to 16384 UTF-8 bytes, argv/environment to 128 entries, mounts to 64 and aggregate copied text to 1048576 bytes. Reject excess before returning intent. |

1. Parse a real request with explicit mounts, environment and workspace. Supply
   a Windows executable and complete argv containing empty and spaced entries.
   Compare all resulting metadata and retain host executable spelling without
   inventing a corresponding guest executable or automatic mount.
2. Compare each typed mount against the existing parser's source, target and
   read-only fields. Preserve authored `HOME`, embedded equals and empty values
   without environment injection or rewriting. Keep relative host identities
   unresolved.
3. Parse a minimal image-only request. Confirm mounts and environment remain
   empty, workspace remains absent and an empty argv entry survives. Do not
   infer repository, executable or HOME mounts.
4. Exercise actual existing parser failures for missing image, unknown network,
   malformed mount and malformed environment assignment. Refuse each exact
   parser error. Refuse the ordinary no-container parser result separately.
5. Reject empty/NUL host identities and NUL argv. Accept ordinary empty argv,
   spaced argv and unresolved relative executable/repository strings.
6. Admit exactly 16384 bytes in a field; refuse a longer executable, argument
   or repository and refuse aggregate copied text above one MiB.
7. Admit 128 arguments, 128 environment entries and 64 real parsed mounts;
   reject the next entry of each kind.

These are construction bounds, not a canonical wire encoding, a filesystem
policy, a resource reservation or provider admission. The adapter does not
claim validation of image syntax, environment policy, mount containment or
guest path compatibility. The existing parser's mount spelling rules remain
its own boundary. No existing launch call site is modified, and this authored
adapter is not evidence of a completed provider migration.

All scenarios remain unexecuted. Runtime, Unicode, backend and platform
compatibility remain unqualified.
