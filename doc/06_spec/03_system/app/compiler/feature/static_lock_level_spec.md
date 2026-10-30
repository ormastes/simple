# Static lock-level ordering

Requirement: REQ-MC-006 / ASYNC-LOCK-ORDER.
Executable: [static_lock_level_spec.spl](../../../../../../test/03_system/app/compiler/feature/static_lock_level_spec.spl).

**Evidence status: UNRUN.** This reviewed companion describes 33 executable
scenarios. It was written manually because no admitted Simple SSpec/docgen
producer exists in this workspace. It is not a generated test receipt.

1. Declare ranked synchronous functions or immutable canonical Mutex resources.
2. Analyze the acquisition sequence through the production frontend.
3. Check acceptance or the precise lock-order diagnostic.

| Scenario group | Expected behavior |
| --- | --- |
| Function ordering | Ascending, equal and zero ranks pass; descending through wrappers rejects |
| Lifetime | Function/Mutex sibling acquisition releases the previous scope |
| Graph safety | Ranked recursive cycles and unresolved/indirect calls reject |
| Metadata | Exact decimal i64, duplicates, dangling/member targets, visibility and reset |
| Resolution | Parameters, imports, resources and canonical helper shadows cannot impersonate owners |
| Scalar safety | Builtin scalar arithmetic passes; nominal operators and changed protected types reject |
| Physical Mutex | Nested method/free-wrapper callbacks follow ranks; same-resource reentry rejects |
| Evaluation order | Keeping arguments run before the new callback acquisition |
| Unsupported boundaries | Manual lock/try_lock/unlock, alias escape, referenced callbacks, async and exemptions reject |
| Cache | Valid metadata restores; descending cache admission and invalid IDs/kinds/duplicates/old versions reject |
| Bounds | Excess proof work rejects instead of returning success |

<details><summary>Executable details and qualification</summary>

The executable uses `check_lock_level_source`, `expect_lock_level_error`, and
`expect_lock_level_success` against the production parser and checker. Cache
scenarios invoke the production flat snapshot and bridge restoration owners.
These are frontend admission tests, not proof of machine-code execution or
runtime mutex correctness. Native CLI rejection before side effects,
interpreter execution, cache/RSS stress, docgen and sspec-maintain still require
the admitted producer and actual execution receipts.

</details>
