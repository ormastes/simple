# FileFiber TLDR Async Bridge System Specification

**Status:** Authored manual; executable qualification is **UNRUN**. This manual
has not been generated from the SSpec by the qualified runtime.

**Requirement:** `REQ-FILEFIBER-TLDR-BRIDGE-001`

**Executable source:**
[`test/03_system/compiler/file_fiber_tldr_async_bridge_spec.spl`](../../../../test/03_system/compiler/file_fiber_tldr_async_bridge_spec.spl)

The SSpec contains three scenarios. Each drives the real FileFiber carrier in
bounded rounds and checks scheduler state or actual SourceReader publication.
These are source-level assertions only until the qualified runtime executes
the specification.

## Local dependency owner progress

**Scenario:** “parks a local importer, progresses past an unrelated producer,
publishes, and closes”

1. Dispatch and acknowledge the first consumer parse.
2. Let the consumer subscribe while both producer fibers remain unparsed.
3. Complete the local producer and observe the consumer resume.
4. Acknowledge unrelated work and close the async scope.

The scenario checks the canonical TLDR wait token and parked state, verifies
the unrelated producer is not a barrier to local producer admission, and
requires the consumer to resume without an error before scope cleanup.

## Real outside SourceReader producer

**Scenario:** “uses FileReader for a real source and preserves one completion
per joined ring token”

1. Run real FileFiber steps until two consumers park on the same key.
2. Fill through the actual FileReader adapter and drain retained ring results.

The fixture writes a temporary source file, dispatches one outside fill, and
checks that both consumers complete, the ring is drained, and the parsed
module text is present before closing the scope.

## Real missing-file failure

**Scenario:** “publishes a real missing-file failure to joined consumers and
closes after drain”

1. Run both real carrier fibers until they join the outside source claim.
2. Let the actual FileReader publish its missing-file diagnostic.

The scenario first ensures its unique missing-file path is absent. It then
checks that both consumers receive the same nonempty diagnostic, that only one
fill is dispatched, that wait records and ring occupancy drain to zero, and
that the scope closes.

## Limits and execution status

- The system scenarios use the explicit async constructor. The legacy FileFiber
  default remains outside this specification.
- Temporary source files and directories are scoped to each scenario and use
  the process ID in their names.
- All bounded loops fail through their scenario assertions if the expected
  scheduler or publication event does not occur.
- No runtime, compiler, or test command was launched for this revision.
  Qualification, generated-manual comparison, and runtime behavior remain
  unverified.
