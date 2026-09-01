# MC/DC Unique Table Boolean Occupancy Misreads on Stage 2 Native

Date: 2026-08-25
Status: source fix present / verification pending

## Reproducer and evidence

The focused Stage 2 native smoke analyzes two evaluations of a two-condition
decision. Condition 0 changes false→true, condition 1 remains false, and the
decision outcome changes false→true, so exactly one unique-cause pair exists.

Three focused compile/run cycles produced:

```text
mcdc-analysis-count-failed:0:rows=4:signatures=4
```

All four condition/evaluation rows were admitted, but the table treated both
rows for each condition as distinct signatures. This matches the repository's
known native Boolean-array read hazard; explicit Boolean normalization did not
repair class-field occupancy state.

## Pending fix

`McdcUniqueTable.used: [bool]` was replaced by integer occupancy markers. This
keeps the lookup branch scalar and allocation-free while avoiding the unstable
Boolean-array representation. The next run confirmed the occupancy portion:
`rows=4:signatures=2`. Pair selection still returned zero, isolating a second
Boolean combination-dispatch hazard. Target value and outcome are now converted
to an integer four-state key before matching. That replacement remains pending
the next focused run. It must require `covered_count=1`, condition 0 covered,
condition 1 uncovered, and two unique signatures.

## Implementation update (unverified)

The analyzer no longer uses Boolean occupancy or Boolean pair-dispatch state.
Occupancy and the target/outcome combination are integer-coded, and signature
keys are fixed scalar triples per mask word rather than allocated key arrays.
The analyzer also has explicit `McdcConditionPolicy` projection masks and
separate unique-cause/masking classifications. This is the intended source fix,
but the admitted self-hosted runtime has not executed the focused analyzer spec
after the broader change. Keep this record open until the exact expected pair/
classification and native/interpreter parity are observed.
