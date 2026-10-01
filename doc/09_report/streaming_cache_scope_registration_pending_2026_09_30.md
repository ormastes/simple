# Streaming frontend cold cache serialization nests an already-owned transient scope

Status: evidence captured; canonical BugDatabase registration blocked.
No canonical bug ID has been allocated. This report is not a registered bug
record and must not be used as the `bug=` value of a workaround annotation.

The Linux early Phase 3 diagnostic loaded 1,594 logical sources, then its third
attempt aborted with SIGABRT (exit -6) after 18.634 seconds at the first parse:
`transient cache serialization scope unavailable`.

Producer SHA256:
`9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`.
Frozen source revision: `0dedfd36ee57ecb6f53b1df163268e82219ff172`.
Serialization helper introduction: `9f28ed3d080`.
Authoritative diagnostic report:
`D:/dev/simple-linux-early-phase3-20260930/RESULT.md`.
Linux result receipt:
`/mnt/simple-bootstrap-6b2/linux-early-phase3-908-20260930/phase3-attempt3/result.json`.

Source diagnosis: `add_streaming_module_surface` already owns the per-file
transient scope when it calls the ordinary frontend parser. On a cold frontend
cache miss, `flat_pools_dump_for_cache` tries to open another scope. The runtime
rejects nesting and the helper panics. This is a source explanation correlated
with the observed failure; no stack capture was collected.

The permanent owner is the Linux early Phase 3 lane. Its proposed correction
carries explicit caller-owned scope state to serialization, preserving both
borrowed and serializer-owned lifetimes. The retained producer requires a
rebuild before that correction can affect its behavior.

The prepared, unexecuted `run-attempt4.py` contains a temporary diagnostic
`baseenv['SIMPLE_FRONTEND_CACHE'] = '0'` block. It preserves native/object cache
reuse but bypasses the defective frontend cache path; it proves no repair.
The block cannot yet receive a valid `@workaround bug=` annotation because
canonical registration remains pending. Retry remains NOT RUN.

## Registration blocker and next action

`src/lib/nogc_sync_mut/database/bug.spl` requires updates through BugDatabase.
`src/app/bug_add/main.spl` is the supported owner: it loads canonical state,
adds the record, and saves through database code that owns CRC/interner/WAL
semantics. No supported offline registrar or bug-create MCP tool was found.
The available generic MCP runner has neither an isolated-cwd parameter nor
verified runner provenance. The available admitted Windows Stage 2 compiler
does not establish general CLI support; its already-recorded help probes
returned exit 1 without output. No Rust seed or hand-edited SDN fallback was used.

Once a qualified CLI is available, run `bug-add` from the isolated feature
checkout with a newly allocated canonical ID, severity P1, the title above,
and the source owner/line from the Linux report. Read the resulting record
through BugDatabase and verify the saved database before sharing that ID.
Then place the marker immediately before only the temporary cache-disable
block; keep the original DB patch and the narrow annotation reviewable.

Pending command, with working directory `D:/wk-workaround-tags-20260930`:

```text
<qualified-self-hosted-cli> bug-add --id=<new-canonical-id> --severity=p1 --title="Streaming frontend cold cache serialization nests an already-owned transient scope" --file=src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl --line=1231 --date=2026-09-30
```

Angle-bracket fields are unresolved prerequisites, not an allocated ID or a
runnable command. Check the ID against both active and archived canonical bug
tables before adding it; verify the source line against the recorded revision.
If a corrected producer becomes available before a full CLI, a focused native
`src/app/bug_add/main.spl` executable may be built in this isolated lane. Its
tool acceptance must first prove help/argument handling, a scratch-database
add/save/read round trip, and CRC/interner/WAL behavior. Only then may it mutate
the isolated canonical database. This is queued work, not an executed build or
permission to fall back to the Rust seed.

Neither the root dirty database nor any derived workaround index was changed.
