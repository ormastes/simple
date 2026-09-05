# RISC-V UART Runtime Owner Contract

The static source contract requires one raw `rt_riscv_uart_put(u64)`
declaration across `src/os/kernel/**/*.spl`, owned by
`arch/riscv/uart_runtime_owner.spl`. Fourteen architecture and no-allocation
consumers must import and call its inline `u8` wrapper.

Source: `test/01_unit/os/kernel/arch/riscv_uart_runtime_owner_contract_spec.spl`

Evidence class: static source contract. It does not prove live UART behavior.

## Purpose and audience

This manual is for SimpleOS HAL maintainers reviewing raw-runtime ownership.
It makes declaration ownership, consumer routing, unsafe-baseline migration,
and the unresolved provider obligation independently auditable.

## Preconditions

- Run from the repository root.
- `rg` must be available because the executable contract searches the complete
  kernel Simple-source scope.
- The listed source and baseline files must be present in the checkout.
- No RISC-V hardware, QEMU image, or compiled artifact is required.

## Scorecard

| Scenarios | Active | Skipped | Pending |
|-----------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

| Static obligation | Expected result |
|-------------------|-----------------|
| Raw declaration ownership | Exactly one matching kernel `.spl` file: the owner |
| Consumer routing | All 14 files import and call `riscv_uart_put` |
| Consumer isolation | No migrated file declares or calls the raw symbol |
| Unsafe baseline | One owner row; all 14 consumer rows absent |
| Provider tracking | `rt_riscv_uart_put` remains in the unbacked baseline |

## Operator workflow

Run:

```text
bin/simple test test/01_unit/os/kernel/arch/riscv_uart_runtime_owner_contract_spec.spl
```

A pass establishes only the static obligations in the scorecard. Use the
RISC-V QEMU or hardware boot gates separately for behavioral UART evidence.

## Scenario narratives and executable evidence

### Keeps the raw u64 ABI behind one typed inline byte owner

1. Read the owner and require the raw `u64` declaration.
2. Require the `@inline` public `u8` wrapper and its widening call.
3. Search every `src/os/kernel/**/*.spl` file for an anchored raw declaration.
4. Require the search result to name only the canonical owner.

<details>
<summary>Executable contract excerpt</summary>

```simple
step("Read and inspect the typed RISC-V UART runtime owner")
val owner = file_read_text(OWNER_PATH)
expect(owner).to_contain("extern fn rt_riscv_uart_put(byte: u64)")
expect(owner).to_contain("@inline\npub fn riscv_uart_put(byte: u8):")
expect(owner).to_contain("rt_riscv_uart_put(byte as u64)")
step("Search every kernel Simple source for anchored raw declarations")
val raw_declarations = process_run("rg", [
    "-l", "^extern fn rt_riscv_uart_put", "src/os/kernel", "--glob", "*.spl"
])
expect(raw_declarations.2).to_equal(0)
expect(raw_declarations.0).to_equal(
    "src/os/kernel/arch/riscv/uart_runtime_owner.spl\n"
)
```

</details>

### Routes every migrated consumer through the owner

For each of the 14 enumerated consumers, the contract requires the canonical
import and at least one wrapper call. It independently rejects raw declarations
and raw calls, so an unused import cannot satisfy the scenario.

<details>
<summary>Executable contract excerpt</summary>

```simple
step("Inspect all 14 migrated architecture and noalloc consumers")
for path in CONSUMER_PATHS:
    val source = file_read_text(path)
    expect(source).to_contain("use os.kernel.arch.riscv.uart_runtime_owner.{riscv_uart_put}")
    expect(source).to_contain("riscv_uart_put(")
    expect(source.contains("extern fn rt_riscv_uart_put")).to_be(false)
    expect(source.contains("rt_riscv_uart_put(")).to_be(false)
```

</details>

### Moves every unsafe row and retains the provider obligation

The contract requires the owner baseline row, rejects the exact row for each of
the same 14 consumers, and requires the unbacked-provider baseline to keep the
runtime symbol visible.

<details>
<summary>Executable contract excerpt</summary>

```simple
step("Read the raw-SFFI and unbacked-provider baselines")
val baseline = file_read_text(BASELINE_PATH)
val unbacked = file_read_text(UNBACKED_PATH)
step("Require the owner row and reject every migrated consumer row")
expect(baseline).to_contain(
    "src/os/kernel/arch/riscv/uart_runtime_owner.spl\trt_riscv_uart_put\t"
)
for path in CONSUMER_PATHS:
    expect(baseline.contains(path + "\trt_riscv_uart_put\t")).to_be(false)
step("Keep the runtime provider obligation explicit")
expect(unbacked).to_contain("rt_riscv_uart_put")
```

</details>

## Findings and remediation

- A second anchored raw declaration means ownership regressed: remove the leaf
  declaration and route that consumer through the typed owner.
- A missing wrapper call means the import is dead or the consumer bypasses the
  owner: preserve its existing byte order and route the emission call.
- A remaining consumer baseline row means the unsafe inventory was not moved:
  remove that exact row after the source migration.
- A missing unbacked entry means provider debt was hidden: restore the symbol
  until every supported target supplies and proves its runtime implementation.

## Evidence and provenance

The source paths are an explicit frozen list in the executable spec. Global
sole ownership is established by an anchored `rg` search over all kernel `.spl`
files, not inferred from that list. Baseline assertions use exact path and
symbol fields. Evidence is reproducible from the checked-out repository and
does not depend on generated or flattened sources.

## Compatibility and limitations

The external provider ABI remains `u64`. The wrapper accepts `u8` and widens
directly; existing consumer APIs retain their prior widths and explicitly
narrow at the owner boundary, matching byte-oriented provider behavior. The
contract does not measure timing, allocations, code generation, QEMU output,
or physical UART output and does not replace those runtime gates.
