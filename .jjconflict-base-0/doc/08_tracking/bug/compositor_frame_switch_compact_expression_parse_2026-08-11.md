# Compositor frame-switch compact-expression parse regression

## Status

Source repaired; execution remains blocked by deployed runtime skew.

## Repair

The retained-damage compositor additions placed expressions after a bare `=`
newline and placed a `Some` payload after `Some(` on the following line. The
current parser rejected these forms with `expected expression, found Newline`.
The expressions now begin on the assignment/call line without changing damage
or cache behavior.

Both focused compositor specs previously stopped at parse time. After repair,
`engine2d_frame_switch_receipt_spec.spl` executes four cases and reports 3 pass
/ 1 fail; the remaining failure is the deployed CLI's missing
`rt_is_interpreter_runtime` extern, tracked with the other deployment-skew
externs. No 8K/80 or device-present conclusion follows from this partial run.
