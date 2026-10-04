# Provider-owned Mach-O link-time run paths

Seven authored scenarios trace ITEM4-REQ-006 in
`test/03_system/app/compiler/feature/item4_macho_rpath_spec.spl`.
**Simple execution UNRUN**; this manual is not generated execution evidence.

| Scenario | Actual assertion |
|---|---|
| V2 filesystem lookup | Bare and suffixed loader/executable tokens and explicit SDK absolute paths return exact real file bytes. Incorrect owner provenance and unsupported relative runpaths reject. |
| Conflicting owner contexts | Distinct real roots resolve one install name to different physical leaf paths; the ambiguity rejects and preserves the destination instead of reusing an install-name-only cache. |
| Inline cycles | The production V2 closure finds reachable inline exports, preserves root ordinal1 and terminates absent-symbol lookup on a cyclic graph. |
| Owner scope and candidate order | A leaf available only through executable or ancestor run paths cannot satisfy the requesting owner's `@rpath` dependency. A malformed first owner candidate preserves the existing destination even when a later valid candidate exists; removing only the malformed candidate permits the unchanged plan to produce independently inspected bytes. |
| Metadata preservation | Real x64/ARM64 LC_RPATH commands retain their ordered paths. V5 target-scoped metadata selects x64 or ARM64 paths without merging the other target. |
| Malformed commands | Starting from successfully parsed real binaries, command-relative offset outside the command, empty path, and missing NUL reject through the actual binary reader. |
| Native composition | Both CPUs and both binary/v5 providers resolve leaf files relative to their requesting owner. The executable run path deliberately differs. Explicit inline metadata wins over a malformed external candidate. The image has the expected CPU, rebased local pointer, exactly one direct root dependency and outward helper binding ordinal1. |

The fixture recipe records the exact LLVM21.1.8 construction, objdump and
readtapi commands. Those external observations establish fixture metadata only.
The frozen project link-time profile uses owner-only paths; this is not a
universal LLVM compatibility claim and does not implement dyld's inherited
runtime load chain. There is no Darwin loading, code-signing, full-SDK or
whole-process memory qualification claim.

Pending execution with an admitted self-hosted runtime:

```
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_rpath_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts
```

These are authored assertions, not observed runtime passes. Immutable file
identity, inherited dyld runtime behavior and native Darwin qualification remain
outside this link-time acceptance evidence.

Pending execution follows [the item4 native execution gate](item4_linker_execution_gate.md).
This command is an unexecuted recipe, not proof that the current CLI or generated
entry is admitted. Account for all 7 declared scenarios and their actual
assertion behavior; zero reported examples or missing scenario results cannot pass.
