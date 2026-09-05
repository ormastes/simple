# MIR coverage V1 concrete probe attachment

The attachment boundary consumes one finalized catalog, its canonical resolved
probe plan, and an already-built MIR module. It accepts only a bijection: every
planned decision or condition payload has exactly one matching typed MIR probe,
and no concrete probe is extra, duplicated, or source-mismatched.

The attachment records catalog, plan, and canonical probe-list hashes with
`admitted=false`. It does not lower HIR, emit a runtime call, publish coverage,
or change any backend gate. Its publication guard fails closed until a later
admitted runtime/backend lowering phase exists.

The executable specification covers the accepted one-decision/one-condition
case plus duplicate-probe, authored-path mismatch, non-boolean local,
cross-function ownership, duplicate canonical MIR function-name rejection before
ownership matching, and stale catalog-snapshot rejection.
