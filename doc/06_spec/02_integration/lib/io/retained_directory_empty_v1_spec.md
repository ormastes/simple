# Retained empty-template observation specification

Status: SOURCE_AUTHORED_NOT_RUN. Authored mirror; no docgen/native result.

REQ-AGENT-BOOT-005 uses two independently provisioned real private directories:
SIMPLE_AGENT_BOOTSTRAP_EMPTY_TEMPLATE_FIXTURE is empty and
SIMPLE_AGENT_BOOTSTRAP_NONEMPTY_TEMPLATE_FIXTURE contains a real entry. Both are
opened through the actual no-follow retained directory owner. Repeated observations
must remain true for the first and false for the second, preventing shared
directory-cursor EOF from masquerading as emptiness. Descriptors close before
assertions. No directory contents are synthesized into a success record.

This checks the IO mechanism only. Actual immutable-image template provenance,
contained Git execution, sole-primary terminal custody and agent replacement are
separate owner evidence and remain NOT_RUN. Supported native profile is Linux
x86_64; no alternative ABI or raw pathname fallback is selected.
