# Stateless anchored Linux IO extraction

Status: SOURCE_AUTHORED_NOT_RUN. This manual is authored alongside its executable
specification; it has not been generated or validated by SPipe/docgen. No admitted
runtime is available and the current task prohibits another native/build campaign.

The specification calls the extracted production helpers against actual libc.
It checks exact x86_64/aarch64 flag constants and unsupported-architecture zero
(REQ-ANCHORED-IO-001); embedded NUL and the 4095-byte pathname limit
(REQ-ANCHORED-IO-002); empty names needed by AT_EMPTY_PATH
(REQ-ANCHORED-IO-003); actual UTF-8 bytes and NUL termination
(REQ-ANCHORED-IO-004); real root directory descriptor and named-root statx identity
correspondence, output widths and directory type (REQ-ANCHORED-IO-005); and a real
invalid-descriptor refusal (REQ-ANCHORED-IO-006).

Native allocations and the root descriptor are freed/closed before assertions.
The tests create no file, directory, workspace, policy, credential or fabricated
owner. Metadata DATA and raw IO implementation descriptors confer no repository,
root custody, process-origin, mutation, mount or launch authority.

The identity-store wrapper retains its private metadata type and original error
strings. Exact source comparison must additionally confirm unchanged domain
registry, origin-before-mutex order, generation/phase policy, root admission,
publication and cleanup. Execution of these tests, original identity regressions,
fault injection, SPipe generation and manual quality gates remains NOT_RUN.
