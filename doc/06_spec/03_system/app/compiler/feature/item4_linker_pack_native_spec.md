# Native linker pack generations

Requirement: ITEM4-REQ-010. **UNRUN — authored manual, not canonical docgen.**
Executable: `test/03_system/app/compiler/feature/item4_linker_pack_native_spec.spl`.
Platform lane: native Linux with an admitted self-hosted runtime and provider.

Build the actual exported source as a shared provider, using the repository's
native-build shared-target arguments:

```
<admitted-runtime> native-build --entry src/compiler/70.backend/linker/linker_pack_entry.spl --entry-closure --source src --emit-shared --no-mangle --output build/providers/item4-linker.so
```

This command is a prerequisite recipe, **not executed evidence**. Record its
source closure, tool identity, artifact digest and exported symbols before use.
The executable spec fails if the artifact is absent; it does not silently skip.

1. Bind the built artifact's digest and independently expected interface ABI.
2. Load/query/pin the actual provider and publish its linker operation.
3. Replace the generation while the old session remains open. Invoke the old
   native operation and observe the real adapter's unsupported-target receipt.
4. Refuse collection while pinned; close and collect it, then reject its stale
   session.
5. Invoke the replacement and independent static recovery; release and unload
   the replacement after retiring it.

This scenario proves lifecycle behavior only when executed. A rejection returned
through a real mapping is not a successful native link, composition-seal proof,
dependency-closure admission or host recovery/performance qualification.
