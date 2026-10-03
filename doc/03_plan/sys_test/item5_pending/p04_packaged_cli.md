# p04_packaged_cli acceptance criteria

Status: NOT_IMPLEMENTED. Criteria precede intentional failing SSpec skeletons; no executable coverage or PASS is claimed.

## I5-P04-AC01 — activate a compiled Office leaf from its installed manifest

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-011 REQ-015
- Setup: Install a compiled Office provider with admitted manifest artifact digest ABI and variant.
- Action: Invoke an Office command through the packaged core CLI.
- Observable: Require declared output and loaded compiled generation without reading provider source.

## I5-P04-AC02 — activate a compiled UI leaf only when its command is demanded

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-011 REQ-015
- Setup: Install a compiled UI provider and instrument optional mappings and initializations.
- Action: Run minimal core help then invoke the UI command.
- Observable: Require zero optional activation for help and exactly the demanded UI generation after invocation.

## I5-P04-AC03 — reject an installed artifact whose bytes disagree with the manifest digest

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-012 REQ-015
- Setup: Install a manifest and mutate its compiled provider artifact without changing the declared digest.
- Action: Invoke the provider command through the packaged CLI.
- Observable: Require typed digest refusal before mapping initialization or provider effects.

## I5-P04-AC04 — reject installed ABI and variant incompatibility before activation

- Status: NOT_IMPLEMENTED
- Requirements: REQ-011 REQ-012 REQ-015
- Setup: Prepare separate installed ABI-mismatch and target-variant-mismatch fixtures.
- Action: Invoke each manifest-selected provider through the packaged CLI.
- Observable: Require the corresponding stable typed refusal zero initialization and no alternate provider substitution.

## I5-P04-AC05 — preserve argument boundaries and standard input and output bytes

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-011
- Setup: Prepare a compiled command accepting spaces empty Unicode arguments and binary stdin.
- Action: Invoke the installed command with explicit argv and captured stdin stdout stderr.
- Observable: Require exact argument boundaries unchanged byte streams and declared exit status.

## I5-P04-AC06 — fail closed for a missing optional installed provider

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-012
- Setup: Prepare an installed manifest with missing-policy=error whose optional compiled artifact is absent.
- Action: Run minimal core help then demand the absent provider capability.
- Observable: Require successful core help and the declared typed unavailable-capability refusal on demand.

## I5-P04-AC07 — reject a policy-denied command without probing its artifact

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-012
- Setup: Install a valid compiled provider and deny its required capability in policy.
- Action: Invoke its packaged command while recording artifact reads and initialization.
- Observable: Require typed policy refusal zero artifact probes and zero provider effects.

## I5-P04-AC08 — forbid source fallback when the compiled provider is unavailable or rejected

- Status: NOT_IMPLEMENTED
- Requirements: REQ-012 REQ-015
- Setup: Install readable provider source alongside absent and incompatible compiled artifacts.
- Action: Demand both manifest-selected provider variants through the packaged CLI.
- Observable: Require typed compiled-artifact refusal and zero source parsing compilation or fallback execution.

## I5-P04-AC09 — exclude optional Office and UI providers from the minimal core entry closure

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-015
- Setup: Prepare a packaged minimal core and installed Office UI and unrelated tool providers.
- Action: Capture the core startup dependency closure before any optional command demand.
- Observable: Require no optional provider retained roots constructors dynamic libraries or source modules in the core closure.



## I5-P04-AC10 — silently skip only typed missing optional providers under explicit policy

- Status: NOT_IMPLEMENTED
- Requirements: REQ-003 REQ-012 REQ-015
- Setup: Prepare an OPTIONAL provider with missing-policy=SILENT_SKIP and absent compiled artifact plus malformed-digest and capability-denial controls.
- Action: Demand the absent optional capability and both invalid control capabilities through the packaged CLI.
- Observable: Require exit 0 only for typed optional absence with zero source fallback; malformed digest and capability denial remain typed errors with nonzero exit.
