# Named catalog sealed dispatch

**Manual draft; execution and docgen TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_named_dispatch_v1_spec.spl`.
Requirements: REQ-001, REQ-014, REQ-016 in Simple platform unification.

## Select the represented named shapes

Select the catalog's q35 pure-NVMe performance lane, x86_32 initrd filesystem
lane, and both RISC-V filesystem lanes. Check each exact catalog identity and
that its production routing predicate selects sealed execution. The predicate
uses the existing inspection authority; no independent production allowlist
is introduced.

## Refuse an unsupported sealed run

Select `x64-gui`. Check that it is outside the supported sealed shapes and that
the sealed run entrypoint returns false before media preparation or launch.
The ordinary GUI runner remains a separate, unmigrated path.

These tests cover routing and refusal, not host execution or guest boot.
After an admitted self-hosted runtime is available, execute this specification,
generate this manual using SPipe docgen and review its real captures and
zero-stub result. No runtime PASS or generated capture is claimed here.
