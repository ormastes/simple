# Canonical scheduler security contract

Source: `test/01_unit/os/kernel/scheduler/scheduler_security_contract_spec.spl`.
Requirements: `simple_os_enhance` REQ-001, REQ-002, REQ-003, REQ-006.

This manual is authored from the executable scenarios; it is not a generated
docgen receipt. Execution and generated documentation remain
**MissingEvidence** because an admitted current self-hosted runner is absent.

The fixture installs a typed TCB representation in a local scheduler. Its
chosen identities and zero mapping fields are test input; no physical page
root, guest process, or running CPU is attested.

| Scenario | Required observation |
| --- | --- |
| Stable state reporting | Ready, Running, Blocked, Zombie remain 0–3; PreparingExit is 4. |
| Admission fence | Live states admit work; PreparingExit and Zombie reject syscall, FD, and capability work. |
| Default creation | PID-backed identities exist, policy/grants are absent, filesystem access is unbound and denied. |
| One-time managed policy | Binding commits once; a nonempty exact syscall filter grants only its listed calls. |
| Invalid binding | Zero/mismatched child, absent parent, missing lifecycle, and terminal state fail. |
| Explicit root objects | A policy-bound user root needs both separate grants; neither object can be granted twice. |
| Invalid root candidates | Kernel tasks, ordinary children, and missing lifecycle identities cannot receive root objects. |
| Pre-exit transition | Stale generation does not transition; exact transition revokes admission and cannot repeat. |
| Filesystem preservation | Resource and isolation-domain updates retain the bound filesystem root and denial state. |
| Fork restrictions | Child principal/CSpace/audit IDs are fresh, job/limits/filter remain, root and reaper grants are absent. |
