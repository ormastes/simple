# Compiler RSS headroom admission

## BOOTSTRAP-COMPILER-HEADROOM-001

An explicitly requested higher compiler ceiling must preserve the default
policy when absent. The user authorized bounded bootstrap recovery after a
real 6 GiB Job cap failure; the reviewed diagnostic request is 12 GiB.

`SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB` requires an explicit cap, declared
compiler worker count and enforced compiler scope. Both the shell resolver and
watchdog independently admit it below `min(floor(total/4)*3,
floor(available/4)*3)`. Use real MemAvailable, or conservative MemFree when
MemAvailable is absent. Unknown, duplicate, contradictory, fixture, malformed,
overflowing and zero memory facts fail closed. Monitor and aggregate test
scope cannot acquire this override. The requested ceiling must exceed the
existing ceiling and must not implicitly increase the actual cap.

The optional invocation row is reserved, hashed and replayed exactly; absent
historical rows remain absent. Case aliases, duplicates and ambient conflicts
are rejected. Receipts distinguish default, elevated and refused requests and
record actual host facts. Existing native Windows Job enforcement is unchanged.

New executable controls are `bootstrap_compiler_headroom_test.shs`,
`bootstrap_compiler_headroom_boundary_test.shs` and
`bootstrap_compiler_ceiling_transport_test.shs` under `scripts/check`.
A tiny real Windows Job validates the new admission without allocating the
budget or rebuilding a compiler. This feature makes no memory-leak fix claim.
