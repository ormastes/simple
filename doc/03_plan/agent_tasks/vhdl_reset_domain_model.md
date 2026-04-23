# VHDL-PARITY-003: Reset and Clock-Domain Model

Status: Pending
Owner: Task VHDL-PARITY-003 agent
Scope: docs and skipped/pending tests only

## Goal

Define the Simple hardware API and acceptance criteria for reset polarity,
reset synchrony, and named clock domains beyond the current
`@clocked(clk, reset_n)` facade. Implementation remains pending.

## Proposed Simple API

Clock domains are declared with `@domain` on hardware functions that contain
registered behavior:

```simple
@hardware
@domain(name: "pix", clock: pix_clk, reset: pix_rst_n, reset_polarity: "active_low", reset_sync: "async")
fn pixel_counter(enable: bool) -> (count: u8):
    reg count: u8 = 0
    if enable:
        count = count + 1
    return (count: count)
```

The shorthand `@clocked(clk, reset_n)` remains accepted and is equivalent to:

```simple
@domain(name: "default", clock: clk, reset: reset_n, reset_polarity: "active_low", reset_sync: "async")
```

Allowed reset polarity values:
- `active_low`
- `active_high`

Allowed reset synchrony values:
- `async`
- `sync`
- `none`

When `reset_sync: "none"` is used, `reset` must be omitted and every register
must have a synthesis-safe initialization policy or an explicit diagnostic.

## Diagnostics

The compiler must reject:
- Unknown `reset_polarity` or `reset_sync` values.
- `reset_sync: "none"` with a `reset` argument.
- `reset_sync: "async"` or `"sync"` without a `reset` argument.
- Duplicate domain names in the same hardware unit.
- A domain clock or reset expression that is not a hardware input port.
- Implicit reads across two named domains.
- Register assignments that mix domains in one process.
- Reset assignments whose type does not match the registered output.

The compiler may accept clock-domain crossings only through explicit CDC APIs,
for example:

```simple
val synced = cdc_sync_bool(src_domain: "button", dst_domain: "sys", value: button_raw)
```

Until CDC primitives are implemented, every cross-domain read must produce a
hard diagnostic that names the source and destination domains.

## VHDL Output Expectations

For `reset_sync: "async"`:

```vhdl
process(clk, rst_n)
begin
    if rst_n = '0' then
        count <= (others => '0');
    elsif rising_edge(clk) then
        count <= count_next;
    end if;
end process;
```

For `reset_sync: "sync"`:

```vhdl
process(clk)
begin
    if rising_edge(clk) then
        if rst = '1' then
            count <= (others => '0');
        else
            count <= count_next;
        end if;
    end if;
end process;
```

For `reset_sync: "none"`:

```vhdl
process(clk)
begin
    if rising_edge(clk) then
        count <= count_next;
    end if;
end process;
```

Named domains must produce deterministic internal names in generated VHDL,
including process labels such as `pix_domain_process` after VHDL identifier
sanitization. Sanitized domain-name collisions must be hard errors.

## Acceptance Tests

Pending tests are tracked in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` and must remain skipped
until implementation exists. Completion requires runnable tests covering:
- Active-low asynchronous reset process shape.
- Active-high synchronous reset process shape.
- No-reset clocked process shape.
- Named domain process labels and deterministic sanitized names.
- Duplicate sanitized domain names rejected.
- Invalid reset polarity rejected.
- Invalid reset synchrony rejected.
- Missing reset rejected when reset synchrony requires one.
- Reset present rejected when reset synchrony is `none`.
- Implicit cross-domain reads rejected with source and destination names.

Verification commands after implementation:

```sh
bin/simple test test/system/compiler/vhdl_reset_domain_spec.spl
ghdl -a --std=08 build/test/vhdl_reset_domain/*.vhdl
ghdl -r --std=08 reset_domain_tb
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
```
