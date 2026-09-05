# Mission-critical memory-allocation diagnostic config

**Added 2026-08-23.** Module:
`src/compiler/00.common/mission_critical/alloc_diagnostic_config.spl`.
Applied by: `src/compiler/35.semantics/noalloc_checker.spl`.

## The property

Mission-critical code must not dynamically allocate memory. The tree already
expresses this structurally (`src/lib/nogc_async_mut_noalloc` is the
baremetal/no-alloc family) and semantically: `noalloc_checker.spl`'s WP-12
**steady-state gate** rejects any symbol whose `AllocClass` is not
`is_steady_state_safe()` once the startup seal has closed — and the seal closes
automatically when the resolved safety profile is at least `critical`, i.e. in
mission-critical mode.

## What existed before

The gate is **all-or-nothing and has no configuration**:
`check_steady_state_gate(manifest, symbol_names)` rejects `Unbounded` and
`Unknown`, accepts `None`/`InitOnly`/`BoundedPool`, and offers no way to accept
a specific audited symbol.

It is also, today, **latent**: `flight_rules.spl:295` and
`effect_verifier.spl:376` both record that `noalloc_checker` is not wired as a
production build gate. Its only drivers are `90.tools/verify` scanners and unit
specs. This config therefore configures the checker at the library/verify
layer; it does not change what a normal build prints today.

## What the config is

A **scoped, justified opt-out** — deliberately not a global off-switch. A global
disable was considered and rejected: the user's own rationale ("mission critical
should not dynalloc memory") is the reason the check must keep existing, so the
knob narrows the gate at named symbols only.

```
struct McAllocAllowance:   scope: text, justification: text
struct McAllocDiagnosticConfig: allowances: [McAllocAllowance]
```

- **Default:** `McAllocDiagnosticConfig.default()` — empty. Byte-identical to the
  pre-config gate.
- **Scope matching:** exact symbol name, or a module prefix matched **on a dot
  boundary** (`boot` covers `boot.stage1`, never `boot_init_unsafe`). Same
  discipline as `is_bounded_pool_family`, where a bare prefix match was already
  a fixed bug (WP-11).
- **Justification is mandatory.** An allowance with an empty justification grants
  nothing.
- **It can never widen the accepted `AllocClass` set** and has **no severity
  dimension** (warn-vs-error is a separate feature).

## Env knob

```
SIMPLE_MC_ALLOC_ALLOW="scope=justification,other_scope=justification"
```

Parsed by the pure function `parse_alloc_allowances(raw)`. The module itself
reads no environment and holds no module-level state (same discipline as
`00.common/assurance/policy_names.spl`); a caller reads the variable and passes
the string in. Unparseable or unjustified entries are dropped fail-closed.

## The check is never deleted

`steady_state_findings(manifest, symbols, config)` returns **every**
non-steady-state-safe symbol, each tagged `allowed` with its justification.
`format_steady_state_finding` prints an allowed one as
`allowed[steady-state]: ... — permitted by mission-critical alloc config: <why>`.
A configured opt-out is therefore always visible and auditable;
`check_steady_state_gate_with_config` merely filters the *rejection* list.

`check_steady_state_gate` is unchanged and delegates with the default config.

## Spec

`test/01_unit/compiler/semantics/mission_critical_alloc_config_spec.spl` (7/7).
