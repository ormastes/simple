# Provider-owned Mach-O link-time run paths

Four authored scenarios trace ITEM4-REQ-006 in
`test/03_system/app/compiler/feature/item4_macho_rpath_spec.spl`.
**Simple execution UNRUN**; this manual is not generated execution evidence.

| Scenario | Actual assertion |
|---|---|
| Owner scope and candidate order | A leaf available only through the executable's run path cannot satisfy an owner's `@rpath` dependency. A malformed first owner candidate preserves the existing destination even when a later valid candidate exists; removing only the malformed candidate permits the unchanged plan to produce independently inspected bytes. |
| Metadata preservation | Real x64/ARM64 LC_RPATH commands retain their ordered paths. V5 target-scoped metadata selects x64 or ARM64 paths without merging the other target. |
| Malformed commands | Starting from successfully parsed real binaries, command-relative offset outside the command, empty path, and missing NUL reject through the actual binary reader. |
| Native composition | Both CPUs and both binary/v5 providers resolve leaf files relative to their requesting owner. The executable run path deliberately differs. The image has the expected CPU, rebased local pointer, exactly one direct root dependency and outward helper binding ordinal1. |

The fixture recipe records the exact LLVM21.1.8 construction, objdump and
readtapi commands. Those external observations establish fixture metadata only.
The frozen project link-time profile uses owner-only paths; this is not a
universal LLVM compatibility claim and does not implement dyld's inherited
runtime load chain. There is no Darwin loading, code-signing, full-SDK or
whole-process memory qualification claim.

Pending execution with an admitted self-hosted runtime:

```
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_rpath_spec.spl --mode=interpreter
```

Owner-context conflicts, inline priority, and cycle coverage remain under the
shared graph acceptance contract until their corresponding tests are authored;
the four cases above do not claim those additional obligations are complete.
