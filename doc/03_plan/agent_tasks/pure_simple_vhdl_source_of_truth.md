# Pure Simple VHDL Source-of-Truth Migration

**Status:** Pending implementation
**Owner model:** parallel implementation workers with tests/docs coordination
**Acceptance specs:** `test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`

## Goal

Make `src/compiler/**/*.spl` the authoritative VHDL generation path for Python-HDL
parity features. Rust MIR backend work and the Simple source facade may remain
as bootstrap/reference/compatibility paths, but support claims move to pure
Simple only when the pure-Simple specs are runnable.

## Worker Assignments

### Worker 1: Structured Hardware Metadata

Owns pure Simple parser/lowering/compiler metadata modules.

- Preserve `@hardware` as structured metadata.
- Preserve `@generic(...)` declarations and defaults as structured metadata.
- Preserve `@clocked(...)` clock, reset, polarity, synchrony, and domain names.
- Preserve labeled tuple return field names through pure Simple IR.

Acceptance:
- `pure Simple compiler preserves @hardware metadata through AST HIR and MIR`
- `pure Simple compiler preserves @generic metadata as structured VHDL generics`
- `pure Simple compiler preserves @clocked reset-domain metadata without source facade parsing`
- `pure Simple compiler preserves labeled tuple return names through MIR`

### Worker 2: Pure Simple Return ABI

Owns pure Simple VHDL entity/port emission.

- Scalar returns emit `result_out`.
- labeled tuple returns emit sanitized output ports.
- anonymous tuple returns emit deterministic `outN` only when allowed.
- reject same-type anonymous hardware outputs.
- reject sanitized collisions across entity, input, and output names.

Acceptance:
- `pure Simple VHDL backend emits labeled tuple output ports from structured IR`
- collision and repeated anonymous-return pending backlog entries.

### Worker 3: Pure Simple Hardware Calls

Owns pure Simple call lowering and virtual aggregate values.

- Select direct `@hardware` callees.
- Emit deterministic entity instances.
- Emit named `port map` connections.
- Allocate deterministic temp signals for multi-output calls.
- Resolve `lo.sum`, `lo.cout`, `lo.0`, and `lo.1`.
- Reject dynamic/runtime tuple access in hardware lowering.

Acceptance:
- `pure Simple VHDL backend lowers direct hardware calls to named entity port maps`
- `pure Simple VHDL backend resolves hardware-call field access from virtual aggregates`
- `pure Simple VHDL backend rejects dynamic runtime tuple access before emission`

### Worker 4: Fixed-Width and Domain Semantics

Owns typed pure Simple hardware operations and clock-domain validation.

- Lower slices, concat, shifts, comparisons, casts, and resize operations from
  typed IR, not facade string parsing.
- Define width and signedness diagnostics.
- Lower named domains, reset polarity, reset synchrony, and no-reset domains.
- Reject implicit cross-domain reads.

Acceptance:
- `pure Simple VHDL backend validates fixed-width slices concat shifts and comparisons from typed IR`
- `pure Simple VHDL backend lowers named clock domains and reset policies from structured metadata`
- `pure Simple VHDL backend rejects implicit clock-domain crossing reads`

### Worker 5: GHDL and Artifact Discipline

Owns generated-file acceptance and diagnostics.

- Run GHDL analyze/elaborate/synth for pure Simple full_add and add2 fixtures.
- Ensure failed VHDL lowering does not leave stale or partial artifacts.
- Keep outputs byte-stable for repeated compilation.

Acceptance:
- `pure Simple VHDL backend generated multi-entity design passes GHDL analyze elaborate and synth`
- `generated pure Simple full_add VHDL passes GHDL analyze elaborate and synth`
- `generated pure Simple add2 caller callee VHDL passes GHDL analyze elaborate and synth`
- `pure Simple diagnostics prevent writing stale or partial VHDL files`

### Worker 6: Specs and Migration Docs

Owns docs/tests only.

- Keep pure-Simple specs pending until implemented.
- Keep facade and Rust MIR claims clearly demoted where pure Simple does not own
  the behavior.
- Promote pending specs to runnable only when implementation workers land.

Current output:
- `test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`
- `test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip`
- `doc/04_architecture/vhdl_support_matrix.md`

## Verification

Run after docs/spec edits:

```sh
bin/simple test test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
```

Run after implementation edits:

```sh
bin/simple test test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl
bin/simple test test/system/compiler/vhdl_source_facade_spec.spl
sh scripts/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check-mcp-native-smoke.shs
```
