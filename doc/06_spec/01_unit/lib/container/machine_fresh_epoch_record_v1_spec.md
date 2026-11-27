# Canonical fresh epoch accounting records

Status: **AUTHORED_NOT_RUN**. Source:
`test/01_unit/lib/container/machine_fresh_epoch_record_v1_spec.spl`.
No compiler, test runner or docgen was invoked.

Five source scenarios exercise production data codecs and validators:

1. Charge outside, overhead and usable partition through the existing Host
   subtract-before-sum validator, with four exact replayed rows and zero
   remaining capacity for the chosen complete-allocation data.
2. Reject overflowing outside obligations, increased usable capacity and
   missing overhead without summing unchecked resource values.
3. Preserve stable installation binding when historical process/manager/slot
   observations differ, while rejecting a changed native store binding.
4. Decode exact canonical original bytes, and reject noncanonical input,
   altered timestamps and incomplete history.
5. Record one unknown creator intent and Update the existing uncertain overhead
   debit; reject replay with another template rather than adding a budget pool.

These are public accounting data fixtures and modeled sequence numbers. They
do not construct genuine preparation, native custody, a machine writer or a
launch grant. No synthetic row is used as native admission evidence. Actual
same-writer publication and profiled creation require the separate installed
fixture scenario and remain NOT_RUN.
