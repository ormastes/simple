# WmWorld focused SPipe native executable exits 139

- **Status:** OPEN — release-blocking for the scoped SimpleOS font goal
- **Lane:** Stage2 standalone `font_evidence_runner`, hosted native execution
- **Scope:** `test/01_unit/os/services/wm/wm_world_multi_window_identity_spec.spl`

## Evidence

The focused spec native-build succeeds with 7 compiled, 0 failed, then its
generated executable exits 139 before the runner can report examples. Three
bounded fix/verify cycles reproduced the same exit:

1. Initial non-generic `WmWindowRow` storage.
2. Host logging disabled through `before_each`.
3. Logging disabled as the first statement of every example and storage
   replaced by index-aligned primitive arrays.

The third generated binary SHA-256 was
`26c930f611429b0efd2c7f2d0b7fd342b2d79ce5b0f95279116afe17441a59b8`.

In contrast, `test/fixtures/os/wm_world_native_smoke.spl` builds with the same
Stage2/runtime pair and exits normally under GDB after spawn, lookup, middle
despawn, and entity/storage reuse. This isolates the remaining crash to the
full generated SPipe executable or its additional linked surface, not the
standalone WmWorld behavior.

## Next bounded action

Start a fresh session. Preserve the generated spec binary instead of allowing
runner cleanup, capture one debugger backtrace, then fix that exact frame.
Do not rerun the unchanged spec in this session: its three-cycle cap is spent.
