# Compiler identity and backend capability

**Manual draft; execution and docgen TEST_BLOCKED.**
Source: `test/01_unit/os/simpleos_compiler_admission_spec.spl`.
Requirements: platform REQ-001 and REQ-016.

These unit scenarios check the existing version and backend-capability owner.
They reject seed banners on either output stream and failed/empty version
responses. A controlled shell shim hides its seed banner when warnings are
suppressed. The scenario suppresses warnings in its caller environment, then
requires the production probe to force the banner visible and reject it.
Caller environment values are restored before the outcome is asserted.

Other shims exercise the LLVM canary, wrong-output refusal, failed backend
refusal and deduplication of candidate aliases. The compiler must produce and
execute the expected canary result for that capability check to succeed.

Shims are intentional unit doubles; their results do not admit provenance or
qualify an actual self-hosted compiler. These shell fixtures require a host
that can execute their shell programs. Actual Linux/Windows compiler admission
belongs to the real CLI acceptance suite; neither host currently has passing
evidence for this change.
