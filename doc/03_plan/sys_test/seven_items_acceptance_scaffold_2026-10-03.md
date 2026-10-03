# Seven-item acceptance scaffold

Date: 2026-10-03. Status: criteria-first authoring; new scenario bodies are
**NOT_IMPLEMENTED**, and none have executed. This is not a feature completion,
verification, admission, or release report.

Scope comes from the [seven-item host completion plan](../seven_plans_host_completion_2026-09-29.md).
The seven items below are distinct features; item 5 additionally has seven
internal work packages. Existing research, requirements, implementations and
test bodies remain authoritative and unchanged.

| Item | Acceptance criteria | Pending modern SSpec |
|---|---|---|
| 1. Platform, parser, dynload and release | [list](seven_items_pending/item01_platform.md) | [spec](../../../test/03_system/seven_items_pending/item01_platform_spec.spl) |
| 2. SCV, jj and GitHub textual databases | [list](seven_items_pending/item02_scv.md) | [spec](../../../test/03_system/seven_items_pending/item02_scv_spec.spl) |
| 3. Typed DataFrame collections and optimizer | [list](seven_items_pending/item03_dataframe.md) | [spec](../../../test/03_system/seven_items_pending/item03_dataframe_spec.spl) |
| 4. mold-based MDSOC++ linker | [list](seven_items_pending/item04_linker.md) | [spec](../../../test/03_system/seven_items_pending/item04_linker_spec.spl) |
| 5. Kernel/extension aspects and binary size | [existing 69 criteria across seven packages](item5_implementation_scaffold_2026-10-03.md) | [existing package specs](../../../test/03_system/runtime/provider/item5_pending/) |
| 6. Compile optimization | [list](seven_items_pending/item06_compile_optimization.md) | [spec](../../../test/03_system/seven_items_pending/item06_compile_optimization_spec.spl) |
| 7. Profile-based container algorithms | [list](seven_items_pending/item07_containers.md) | [spec](../../../test/03_system/seven_items_pending/item07_containers_spec.spl) |

Each new list precedes its spec and records stable acceptance IDs, source
requirements or named plan sections, concrete setup, action, and observable
outcome. Existing component tests do not replace an end-to-end oracle. These
lists add no new requirement selection and do not certify exhaustive closure
of every linked feature plan.

This change adds **55 criteria and 55 pending scenarios**: item 1 has 8,
item 2 has 10, item 3 has 11, item 4 has 9, item 6 has 9, and item 7 has 8.
Together with item 5's existing 69-criterion baseline, the index links 124
scenarios. Later item 5 implementation work is tracked separately and is not
reset to pending by this change.

Each new scenario uses `describe`, `it`, and readable `step("Arrange: ...")`,
`step("Act: ...")`, and `step("Check: ...")` statements. These steps describe
planned work; they perform no product operation. The only terminal behavior
is `fail("NOT_IMPLEMENTED <acceptance ID>: ...")`. File/scenario metadata
retains `in-development`, `not-implemented` and `NOT_IMPLEMENTED` status.
Thus there is no test implementation yet and explicit execution cannot count
an empty body as success. No passing placeholder or no-op helper is supplied.

Windows native and Linux/WSL evidence must be separate. Other supported host,
architecture and object-format cells remain outstanding until measured;
SimpleOS target evidence does not certify a development host. Missing fixtures
or runners never turn into a successful result or an unsupported-scope waiver.

Parallel authoring ownership: `item5_research` owns items 1 and 7;
`item5_cli` owns items 2 and 3; `item5_tdd_audit` owns items 4 and 6.
The parent owns item 5 reuse, common conventions, review, integration and PR
landing. Each agent uses its existing isolated worktree. Only the new scaffold
files belong to this change; earlier source and test implementation edits stay
in their respective lanes.

Next coding phase replaces individual failure markers with actual production
setup, actions and assertions, then separately records execution evidence.
Generated manuals and runtime checks are not claimed for these deliberately
unfinished bodies. Publishing this scaffold does not mark any host/item DONE.
