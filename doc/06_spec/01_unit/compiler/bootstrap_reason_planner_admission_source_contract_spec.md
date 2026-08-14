# Bootstrap reason planner v2 source contract

The planner source admits only `//bootstrap:stage3` and
`//bootstrap:stage4`, with a stage-specific typed-reason enumeration. Its
authorization receipt requires exact lowercase SHA-256 identities for the
parent compiler, frozen runtime, planner source closure, and planner binary.

This static contract does not build or execute the planner.
