# Stage 4 DevHub JSON compatibility facade resolution

Status: repaired; final Stage 4 cycle validation pending
Severity: P1 bootstrap blocker
Owner: pure-Simple JSON compatibility facade and canonical JSON modules
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `53381757447`

## Exact failure

After the cycle-2 `cmd_wiki` function-local import repair, the retained Stage 3
compiler's HIR-focused SMF compile of the real module no longer reported
`process_run`. It crossed into `src/app/devhub/adapter_confluence.spl` and then
failed on unresolved JSON facade names: `json_parse`, `json_object_get`,
`json_array_length`, `json_array_get`, `json_get_type`, and `json_serialize`.

The focused command exited 1 after 2.36s at 130,760 KiB max RSS. No Stage 4
candidate or deployment exists.

Retained evidence:

- `build/focused/stage4-wiki-process/cmd-wiki-smf.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle2.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`

After a direct-owner import split repaired `adapter_confluence`, the same
focused command advanced to `src/app/devhub/output.spl` and reported the same
unresolved `std.json` operations. That second real consumer proved the missing
root facade was shared closure infrastructure rather than an adapter-local
import defect.

## Boundary decision

`std.json` has no physical root module. Focused entry-closure discovery reaches
`std.common.json.__init__`, but its member-star exports do not materialize the
physical JSON modules required by its legacy consumers. `src/lib/json.spl` is
now the compatibility root and explicitly re-exports parser, serializer,
object operations, array operations, and types. Physical declarations remain
in `std.common.json`; no JSON behavior, runtime extern, global fallback, or
compiler resolver policy changed.

## Required regression evidence

1. The real `cmd_wiki`/Confluence HIR-focused SMF route resolves every named
   JSON operation and no longer reports `process_run`.
2. An adjacent direct consumer proves the selected canonical JSON facade.
3. The final full-resource x86 Stage 4 run is cycle 3/3; do not repeat cycle 2.

`test/03_system/native/stage4_json_root_facade_contract.spl` imports parse and
serialize through both the compatibility and canonical routes, retains the
parser's core character dependency, and requires both routes to round-trip the
JSON `null` value. The real `cmd_wiki` SMF route remains the exact multi-consumer
gate.

Focused evidence:

- The facade contract compiled eight modules and exited 30 in 2.47s at 158,464
  KiB max RSS.
- The final capped `cmd_wiki` SMF attempt contained no process or JSON
  diagnostic. It advanced to the separately claimed TUI terminal helper
  blocker.
- Logs are retained in `build/focused/stage4-json-root-facade/`.

## Cycle accounting

- Cycle 1/3: lint enum terminal collision, repaired.
- Cycle 2/3: wiki process import blocker, repaired; this JSON blocker was
  exposed by its focused post-fix shard before cycle 3.
