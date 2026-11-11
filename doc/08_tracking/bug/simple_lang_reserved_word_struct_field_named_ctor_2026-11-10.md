# Simple grammar: struct field named like a reserved word breaks named-argument construction

Status: WORKED AROUND 2026-11-10; language fix owned by the compiler team.

## Symptom

`parse: ... function arguments: expected Comma, found Colon` with NO line
number, reported against the importing file, whenever a struct whose field is
named `spawn` is constructed with named arguments:

```spl
struct ProbeRet:
    a: i64
    spawn: i64

val r = ProbeRet(a: 1, spawn: 3)   # parse error: expected Comma, found Colon
val r = ProbeRet(1, 3)             # positional: parses, and r.spawn reads fine
```

Minimal repro verified 2026-11-10 on the Windows interpreter lane. The parser
treats the `spawn:` label as foreign syntax inside the argument list, i.e. the
callee is parsed as an ordinary function call, not a struct constructor.

## Blast radius on release/1.0.0

Blocked 8 caret unit specs (agent_workspace, agent_worktree_release,
cs_dashboard, cs_main, main, multimodal_proxy, pane_backend,
pane_backend_windows) plus the `host_helper_settlement_v1` system spec through
two structs:

- `HostHelperStreamRetainedV1.spawn` (src/lib/nogc_sync_mut/orchestration/host_helper_stream_owner_v1.spl)
- `ContainerOutputTurnV2.spawn` (src/lib/nogc_async_mut/container/stream_v2.spl)

Field DECLARATION and `.spawn` field ACCESS both parse; only named-argument
construction is rejected. Other files declare `spawn:` fields without
constructing them by name and were unaffected.

## Workaround applied

Renamed both fields to `child_spawn` (definition, all named-argument
construction sites, and the one `.spawn` accessor in
host_helper_settlement_v1.spl). Named-argument construction is the house
style; positional construction would have been a fragile workaround.

## Suggested language fix

Either reserve `spawn` (and friends) as illegal struct field names with a
clear diagnostic at the declaration site, or make named-argument parsing
context-aware so a known struct type's field labels parse regardless of
keyword overlap. The current failure mode (line-number-less parse error at
every importer) costs far more to diagnose than either option.
