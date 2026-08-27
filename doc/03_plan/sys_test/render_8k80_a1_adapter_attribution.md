# Render 8K80 A1 adapter-attribution system-test plan

Status: **TEST_BLOCKED** pending an admitted pure-Simple CLI.

## Scope

The system test covers the completed A1 adapter-attribution lane: real wrapper
identity correlation, durable RTX A6000 fingerprint/hash binding, the A1 versus
A6/A8 scope boundary, and typed blocking when the physical display is
unreachable.

Excluded: A4/A5 performance, live physical 8K80 presentation, EDID admission,
captured scanout, and campaign promotion.

## Environment

- Repository root checkout containing the executable spec and mirrored manual.
- Admitted pure-Simple CLI with `test`, `spipe-docgen`, and `sspec-maintain`.
- `sh` plus checked-in render wrappers.
- No Rust seed, interpreter fallback, Xvfb promotion, or synthetic physical
  evidence.

## Execution order

1. Run the focused executable SSpec once.
2. Require all three examples and the runner verdict to pass.
3. Run `sspec-maintain scan` once and inspect all seven component scores,
   blockers, mirror state, and traceability.
4. Run `spipe-docgen` once and require complete documentation with zero stubs.
5. Review the regenerated manual for visible primary steps and folded
   executable detail.

## Pass and fail criteria

PASS requires the real self-test markers, exact durable adapter fields/hash,
A1 checked, A6/A8 open, explicit Xvfb exclusion, and exit `2` with the typed
unreachable-display blocker. Missing fields, changed identity, physical
overclaim, zero exit for the unavailable display, placeholder assertions,
missing examples, or a non-admitted runner fail closed.

Until the CLI requirement is met, the execution result is `TEST_BLOCKED`, not
PASS, skip, or generated evidence.

## Traceability

| Requirement | Executable scenarios | Manual | Coverage |
|---|---:|---|---|
| REQ-R8KC-004 | 3: positive + edge + error | `doc/06_spec/03_system/gui/wm_compare/render_8k80_a1_adapter_attribution_spec.md` | Exact immutable attribution; no unavailable-device receipt promotion |
| REQ-R8KC-006 | 3: positive + edge + error | same | A1 remains bounded; physical rows stay open; unavailable display blocks |
| NFR-R8KC-004 | 3: positive + edge + error | same | Valid correlation passes; invalid/unavailable inputs fail closed |
| NFR-R8KC-006 | 3: positive + edge + error | same | Xvfb/unavailable display never promote scanout |

## Manual rendering policy

Show the three scenario narratives and their `step("...")` flow. Keep the
executable source folded below the operator workflow after regeneration. Link
text/exec evidence rather than embedding large logs. No screenshot is required
because this lane verifies receipt identity and classification, not pixels.

## Risks

- A runner may crash or report a false-green prefix; require the full
  three-example verdict.
- A future report edit may preserve the adapter name but lose the stable hash.
- A future plan edit may close A1 while accidentally promoting A6/A8.
- An unavailable display may be misclassified as PASS instead of blocked.
