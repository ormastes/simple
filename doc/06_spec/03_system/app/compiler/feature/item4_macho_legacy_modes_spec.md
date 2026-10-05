# Legacy Mach-O dependency command modes

Requirement: ITEM4-REQ-006. Executable source: [item4_macho_legacy_modes_spec.spl](../../../../../../test/03_system/app/compiler/feature/item4_macho_legacy_modes_spec.spl).

**Simple execution UNRUN.** This is an authored companion, not a generated SPipe execution receipt. No runtime, host-loader, signing acceptance or full SDK qualification is claimed.

| Scenario | Actual operation and assertions |
| --- | --- |
| Present weak versus lazy/upward dependency | Read a real binary selector provider; change only its existing LC_LOAD_DYLIB command to weak `0x80000018`, lazy `0x20`, or upward `0x80000023`; validate the changed provider through the production reader. Stage the actual dependency in an explicit directory. Weak visibility must produce a real executable; lazy/upward must report unresolved hosted imports and preserve the destination sentinel. |
| Matched dependency missing | Link real importing object and active-selector provider with an empty explicit search directory. Require the missing dependency name and search diagnostic, with the destination bytes unchanged. |
| Unmatched dependency absent | Use the modern, compressed own-export fixture with selector `unmatched` and classic inference disabled. Require its real `_helper`/`_value` exports and successful output despite the dependency being absent. |

The weak scenario tests command-class visibility with a **present provider**. It does not qualify absent weak dependency behavior or weak-import binding semantics; those SDK requirements remain open.

The positive wire oracle independently checks the Mach-O magic, CPU, executable type, local pointer, exactly one outward direct-root load command, and the bind stream's root ordinal 1 and `_helper` name. All variable command/name/stream offsets are bounded before indexing. Negative cases require specific semantic errors, so a publication failure cannot satisfy the intended assertion.

Fixtures and their external LLVM construction/inspection provenance are in [RECIPE.md](../../../../../../test/fixtures/linker/macho/RECIPE.md). The modern unmatched fixture is supplied by commit `006e145c405`; it deliberately avoids classic inference, which legitimately probes ordinary dependencies even when explicit selectors do not match. Tests create isolated temporary directories and remove only their own named files.

Pending execution with an admitted pure-Simple runtime:

```text
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_legacy_modes_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

Docgen and runtime evidence remain pending; fixture inspection is not Simple execution.

Pending execution follows [the item4 native execution gate](item4_linker_execution_gate.md).
This command is an unexecuted recipe, not proof that the current CLI or generated
entry is admitted. Account for all 3 declared scenarios and their actual
assertion behavior; zero reported examples or missing scenario results cannot pass.
