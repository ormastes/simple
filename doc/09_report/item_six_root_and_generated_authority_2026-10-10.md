# Item six: stable roots and generated-output authority

STATUS: WARN — implementation candidate; runtime verification and landing blocked.

This change targets `release/1.0` from base
`5646a90e73ecf21eeae859e2ff3b31cf1eef4b6e`. It does not mark the seven-item plan,
the item-six 44-scenario system contract, or generated-source support complete.

## Implementation and traceability

The persistent-package-index plan's invalidation rules require private source
edits to reach semantic transition comparison and package-manifest changes to
invalidate only the package and its exact consumers. The cold publisher formerly
used `snapshot.tree_id` as root-generation authority, making every tree edit
incompatible before semantic comparison. The ownership capture now derives an
optional stable root from SCV-validated policy bytes and the policy's explicit
project identity. Revision, commit, tree and inventory witnesses remain separate.
The checked-in policy opts in; absent identity retains conservative legacy
behavior, and malformed identity fails closed. Manifest digests stay per member
so their content changes do not partition the whole project. Policy changes
still conservatively partition the project root.

The generated-source contract requires an independently selected declaration.
The compiled-output bridge previously accepted both declaration and receipt
from the same artifact. It now rejects nonempty generated facets before index
publication because that boundary has no independent declaration authority.
Ordinary source modules use an empty facet. The lower-level receipt consistency
API remains available; this change does not add the missing generator producer.

The ownership unit spec adds source edit, inventory generation, snapshot
relocation, project and ownership-policy separation, per-package manifest
changes, reordered manifests, legacy policy and malformed identity regressions.
The compiled-output spec exercises ordinary output, self-consistent but
self-authorized generated output, refusal before publication and orphan receipt
metadata. These are executable test changes, not executed PASS claims.

## Review and verification

The user-requested smaller-model helper implemented the generated-source gate
and reviewed the stable-root diff. The primary model reviewed the final source,
tests and design, and corrected an initial manifest-inclusive root so it obeys
the plan's exact-consumer invalidation requirement. No other session's dirty
files, runtime processes or compiler candidates were changed.

Working direct-env and numbered-artifact guards passed. The tracked
`doc/06_spec/*_spec.spl` count is zero. The staged direct-env guard also passed.
None of these source checks replaces
runtime tests, branch coverage or generated-manual verification.

The current `rel-p3run` Phase 2 executable hashes to `5d97a3dc...ded2`, but its
provenance and sanity receipts bind `49cbd005...9eb7e`; its current admission
path is missing. The matching archived `49cbd005...9eb7e` compiler-test rejection
is a delegation configuration failure: delegation requires an explicit
`SIMPLE_MCDC_OFF_WAIVER_REASON`, or `BOOTSTRAP_STAGE2_TEST_DELEGATE=0`. It produced
no individual test results. The separate `rel-s2rebuild` candidate lacks matching
admission receipts. No ready compiled SSpec runner was found in those two trees.

An isolated diagnostic with the archived pure-Simple compiler, bounded to 60
seconds, exited 1: `error: unknown command 'check'`. Its log and process receipt
are retained in `build/native_probe/item6-completion/root-check.*`. No seed was
substituted and no admission claim was made from that diagnostic.

A second isolated diagnostic invoked the same compiler with `native-build` on
the absolute ownership-module entry, the compiler/app/lib source roots,
`--entry-closure --emit-object --backend=llvm --threads 1`, and an isolated
preserved cache. With the managed LLVM/MSVC bootstrap environment and
`SIMPLE_NO_STUB_FALLBACK=1`, it reached surface freezing after 359 surface-alias
rows. The 300-second process-group bound expired with status 124 and cleanup
`reaped`; no object or test PASS was produced. The last logged compiler phase
elapsed time was about 80.5 seconds and excludes outer startup/inventory time.
Evidence: `build/native_probe/item6-completion/ownership-compile.log` and its
`.receipt`; log SHA256
`a6e90c193507eef37097f0d7787c787a42b29a5ed4006d1aa5b1da874037521f`.
This bounded startup/compile performance blocker requires an admitted runtime
and a cache-preserving bootstrap repair; do not relabel the timeout as success.
The SCV snapshot captured the earlier manifest-inclusive root implementation
before review corrected it. Its ownership source hash is
`906bad2de2bf682f5cb456e3154251ebd9972b1155f9ccac56f5c39ce583170f`;
the final ownership source hash is
`e5562c25c90171511b90d73fb4fb65281c3945e941a2c7e18b3d5fb18edfdf0a`.
The diagnostic is bootstrap failure evidence, not validation of the final diff.

## Remaining release gate

Provide an exact admitted pure-Simple compiler and test runner, execute the
changed specs, generate and verify their manuals, run the required compiler,
library, MCP and LSP checks and runtime/native smokes, and verify the item-six
system scenarios and performance targets. Independent generated-plan authority
and real generated producers remain unfinished. Preserve the draft until these
requirements establish STATUS: PASS; then review its exact diff/comments and
merge the PR into `release/1.0`.

## Continuing acceptance research and implementation

The next goal turn rebased the isolated integration worktree onto release commit
`8f86655d67f3dda61677a5f3eafa32ec26a2f4a3`; this renews the candidate and does not
carry forward runtime admission from its former base. Session owner is the
primary item-six agent, worktree
`C:/dev/simple-item6-phase2-verify-owner-20261010`, branch
`work/item6-complete-release-20261010`, integration target `release/1.0`.
Smaller-model research, SSpec and generated-projection lanes use separate
`simple-item6-acceptance-contract-20261010`,
`simple-item6-sspec-contract-20261010`, and
`simple-item6-generated-index-20261010` worktrees; primary review remains required.

Source review identified native text-ordering hazards in ownership identifier
validation. The implementation now uses ASCII byte codes; regression cases cover
all allowed character classes, whitespace and non-ASCII rejection. Inventory
fixtures count UTF-8 bytes so non-ASCII policy tests reach the intended validator.

The system spec retains all 44 names, order and original observable assertions,
verified by comparing the before/after source. A shared invocation helper checks
the exact scenario line and rejects the existing owner-only/incomplete markers,
normalizing CRLF line endings. This is an evidence-substitution guard, not proof
of compiler-origin receipts. The mirrored manual preserves that distinction.
The actual checker probe reported that the compiled acceptance owner is absent;
no SSpec execution or TDD red/green result is claimed.

Additional research found generated-source identity is lost between the TLDR
header and compact index entry. The detail design specifies schema-4 projection
and conservative legacy migration; the isolated implementation lane must close
that gap without treating it as generator execution. The domain research records
the separate declaration, action execution, frozen byte admission and semantic
projection requirements. Full runtime qualification and the original 44-scenario
contract remain open.
