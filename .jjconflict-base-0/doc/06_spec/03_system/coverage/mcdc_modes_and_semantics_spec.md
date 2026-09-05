# MC/DC Modes and Semantics — Operator Manual

Executable: `test/03_system/coverage/mcdc_modes_and_semantics_spec.spl`  
Status: **not executed in this lane**. This is a hand-maintained mirror pending standalone SPipe doc generation.

## Claim boundary

The focused scenarios call the production mode model, identity function,
masking analyzer, and dynamic-aspect capsule. The end-to-end scenario additionally
drives `bin/simple compile`, `bin/simple test --mode=native`, the generated test
wrapper, compiler obligation-manifest extraction, child raw-evidence transport,
suite aggregation, and the exact normal-profile report gate. Its retained binary,
exec, and artifact captures are the required release evidence; this source alone
does not claim that they exist.

## Workflow

1. **configure MC/DC mode** — require distinct `off`, `on`, and `dynamic` values and static-off default policy.
2. **exercise independent conditions** — feed the short-circuit `A and B` evaluated/true/masked words and require both exact independence pairs.
3. **load dynamic MC/DC aspect** — require stable identity and a dormant aspect with token `0` and no recorder storage.
4. **configure MC/DC mode** — run the production native test runner in static-on
   mode against three real short-circuit vectors. Require exit zero and the exact
   gate's human diagnostic, proving compile manifest → child evidence → aggregate
   → gate transport rather than calling the analyzer directly.
5. **load dynamic MC/DC aspect** — repeat the same end-to-end runner flow in
   dynamic mode, then compile and execute a lifecycle fixture that observes the
   compiler-loaded aspect, unloads it at a quiescent boundary, and observes it absent.
6. **configure MC/DC mode** — compile identical native fixtures through the
   default and explicit static-off routes and require byte-identical file size,
   no static/dynamic MC/DC symbols in the off artifact, and MC/DC symbols plus a
   bounded obligation manifest in static-on.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-001 | Explicit modes plus production native baseline/off size and symbol inventory |
| REQ-002, REQ-003 | Concrete masking rows and exact analyzer result |
| REQ-007 | Dormant capsule plus production compile/load/unload lifecycle |
| REQ-014 | Repeated canonical identity and runner-owned deterministic aggregation |

## Evidence artifacts

The executable retains binaries under `build/mcdc-system-e2e/` and uses typed
`exec`, `binary`, and `artifact` captures. Missing compiler, malformed/missing
manifest, child evidence failure, exact-gate rejection, lifecycle failure,
`nm` failure, size delta, or an MC/DC symbol in the off artifact fails the
scenario. There is no skip or helper-only fallback.
