# Lazy Module Loader Bridge (W2-A2, AC-4 smoke)

> Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl

<!-- sdn-diagram:id=module_loader_lazy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_lazy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_lazy_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_lazy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Module Loader Bridge (W2-A2, AC-4 smoke)

Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl
directly (no load_module wiring needed):
- outline scan of real modules records the declaration surface only,
- the module is registered through the existing deferred mechanism
  (so the first symbol use materializes it via try_force_any_deferred_for),
- per-function body spans slice back to the exact function source text that
  the materializer parses on first call.

Each scenario runs inside a module-level helper returning "" on success or
an error description; the it blocks assert on that single value. (In
interpreter mode, `it` closures observe stale module state and expects on
non-local expressions can be hollow, so all stateful work happens in
ordinary functions.)

NOTE: actually running the self-hosted parser/eval (force -> load_module ->
parse) is not possible from interpreter-mode specs (same limitation as
test/02_integration/compiler/core_interpreter_intensive_spec.spl); the full
load-equivalence and benchmark coverage is task W2-A1 in compiled mode.

## Scenarios

### lazy module loader bridge

#### outline-scans a real module and defers it with its declaration surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_defers_ctype()
expect(err).to_equal("")
```

</details>

#### records body spans that slice to the exact function source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_slice_to_upper()
expect(err).to_equal("")
```

</details>

#### scans a module with docstrings and quote-heavy literal bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_text_advanced()
expect(err).to_equal("")
```

</details>

#### keeps the default mode gates off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_mode_gates()
expect(err).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
