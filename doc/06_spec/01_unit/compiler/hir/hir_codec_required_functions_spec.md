# Required HIR function payload controls

Status: AUTHORED / NOT_RUN. No compiler or generator execution was performed.

The spec parses and lowers a real `answer` function returning41, checks its body,
and retains legacy stable roundtrip controls. Generated-core controls invoke the
actual canonical bounded writer and bounded reader/generated decoder directly,
check complete frame consumption and byte-stable source-module reencoding.
The independently authored wire fixture enumerates all23 current fields after
functions, including both false booleans and empty metadata collections. Its
valid control must decode before missing-key/missing-value controls can qualify.
The function payload is produced by the real generated function encoder; this
is an independent module-layout fixture, not an independent full-function golden.

Public canonical encode/decode must separately return the exact Unavailable
reason while admission remains closed. Generated-core attempts use separate
budgets; they do not prove public combined decode/reencode budget accounting,
public cache/authority admission, generator reproducibility, independent full-HIR
goldens, or production performance. Those post-admission obligations remain.

Portable completeness-guard mutation was separately exercised with default awk:
one exact field succeeds, absent/duplicate fields fail. This is three mutation
controls only, not a generator/completeness PASS. No gate was opened.

Related portable_hir_semantic_profile_v1 and three_payload_driver_body_authority_v1
specs retain public-success obligations; whole-file success requires future real
canonical admission. Their positive paths must not become Unavailable passes.
