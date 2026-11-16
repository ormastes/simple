# Retained anchored directory staging source specification

Status: SOURCE_AUTHORED_NOT_RUN. Authored mirror, not SPipe-generated evidence.

REQ-AGENT-STAGE-005 requires a real Linux fixture independently provisioned as an
empty private trusted directory, supplied by SIMPLE_AGENT_STAGE_PRIVATE_FIXTURE.
It uses actual retained directory/file IO, creates an exclusive child and writes
three exact bytes, refuses occupied file/directory adoption and traversal, reads
the real destination bytes back, compares the original parent’s named child to
the actual retained child and rejects a different held directory, then consumes
retained descriptors. This checks real directory correspondence, not native quota. Artifacts
remain for operator inspection; the fixture cannot be reused as an empty fixture.

This exercises a lower IO mechanism, not Host invocation authorization. Full
source-owner cases must provision actual installed policy, quota and exclusion,
then invoke through the separately signed same-domain Host effect gate. Missing
policy, changed slot/profile/invocation, source symlink/hardlink/change, quota/write/
sync errors, uncertain partial creation, stale retry and retained close must fail
with original custody held. Those composed runtime scenarios, fault injection,
manual generation and coverage remain NOT_RUN. No Git or Container success is
claimed by this specification.
