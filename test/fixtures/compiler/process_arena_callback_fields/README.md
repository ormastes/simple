# Actual process arena callback fields (#2980)

`main.spl` exercises the production process_task_arena module and checks all
host callback fields through its public lifecycle. Success requires exit 0
and `process-arena-callback-fields: pass`; object output alone is not execution
proof. Run using the admitted pure-Simple producer with
`SIMPLE_NO_STUB_FALLBACK=1`, isolated cache, pinned source/runtime identities,
and the reviewed monitor-only watchdog. Native qualification is pending.
