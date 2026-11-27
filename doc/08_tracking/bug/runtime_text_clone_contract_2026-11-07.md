# Native text cloning and embedded-NUL ordering

## Defects on release snapshot 11fb1f49b698

Both `rt_string_concat` and `rt_strcat_tagged` returned the nil value when
allocation or string registration failed. An infallible text Clone implemented
through ordinary concatenation could therefore appear to succeed with a nontext
result. The first entrypoint guarded only the payload sum, leaving header and
terminator overflow; the tagged entrypoint also lacked the payload-sum check.

`rt_text_cmp_any` used strcmp even for length-delimited tagged strings, so
`a\0z` and `a\0a` compared equal. A compiled probe against the unchanged
release source reproduced result0 and exited1 for an expected positive result.

## Repair

Both concat entrypoints use one checked byte-allocation owner. It validates
the unsigned payload sum and complete size_t allocation including header and
terminator. Failed conversion, allocation, or registration follows the existing
nonreturning `spl_panic` contract; registration failure frees the unregistered
allocation. The tagged entrypoint preserves its raw-pointer/nil fallback and
uses stored lengths for tagged input, including embedded NULs.

Ordering compares common bytes with memcmp and then lengths. Raw fallback
semantics are preserved. Cache receipt compatibility is covered by the focused
reverse-reference spec: an old admissible NUL receipt retains its bytes; old
strcmp-tied multirow order was already inadmissible and has a different corrected
canonical encoding. This is not a blanket claim that all historical bytes stay
unchanged or that a new cache schema has been qualified.

## Evidence and limits

`src/runtime/test/rt_text_clone_contract_selfcheck.c` includes the actual native
owner. Thirty-one checks passed once under the canonical30-second process-tree
watchdog on Darwin. Checks cover two entrypoints, fresh independent lifetime,
empty/NUL/supplementary Unicode bytes, raw/nil fallback, both allocation fault
branches, payload/header overflow and NUL/prefix ordering. Compile-time-only fault
controls affect the real allocation/registration branch. The explicit panic stub
records the nonreturning call as exit101 and checks unchanged registry count;
it does not qualify the language unwinder. A baseline probe against11fb1f49
compiled successfully and reproduced the old ordering defect (exit1).

The Simple cache fixtures and builtin text provider tests remain AUTHORED /
NOT_RUN. No full compiler, builtin-trait matrix, bootstrap, or platform parity
completion follows from these focused native checks. Source review and landing
remain required. Local full logs/receipts are retained under
`/private/tmp/release100-eight-lane-20261107/lane4/text-native`.
