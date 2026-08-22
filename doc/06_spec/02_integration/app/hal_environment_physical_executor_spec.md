# Hosted HAL Environment Physical Executor

This integration specification demonstrates bounded physical capture and exact
replay for runtime/HAL environment instructions.

## Ambient environment capture

1. Prepare `EnvironmentGet(PATH)` before sealing; preparation performs the only
   ambient lookup and retains at most 64 KiB.
2. Create the parent cursor for invocation 31 and provide caller-owned argument
   and result regions.
3. Confirm a different invocation identity is rejected without changing the
   result region.
4. Consume the canonical cursor once and confirm the receipt records zero
   post-seal allocations.
5. Confirm duplicate consumption is rejected without result mutation.
6. Replay the accepted observation into separate caller storage and confirm
   byte equality with `physical_effect=false`.

## Clock capture

1. Capture one clock value during preparation and create the invocation-bound
   parent cursor.
2. Confirm policy without nondeterminism authority rejects the instruction and
   leaves output untouched.
3. Execute once with authority and confirm exactly eight captured bytes and
   zero post-seal allocations.
4. Confirm the consumed cursor rejects a duplicate without output mutation.
5. Replay into separate caller storage and confirm identical bytes with no
   clock access.

The executable source is
`test/02_integration/app/hal_environment_physical_executor_spec.spl`.
