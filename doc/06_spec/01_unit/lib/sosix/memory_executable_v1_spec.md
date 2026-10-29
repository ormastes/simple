# SOSIX admitted executable identity

Executable specification: `test/01_unit/lib/sosix/memory_executable_v1_spec.spl`.

The hosted SOSIX image owner compares the actual immutable image digest with
the canonical SHA-256 admitted by a caller. BuildRunner uses this after pinning
its staged producer, before starting a process. The four examples cover a
matching 32-byte digest, a changed digest, missing/truncated provider digests,
and noncanonical or empty expected digest text.

Diagnostic P1 interpreter evidence on 2026-10-29: 4 examples executed, 4 passed,
0 failed, 0 skipped. This is pure digest-contract evidence. It does not prove
native pin creation or grouped process execution. The separate native owner
spec and smoke entry require the native runtime adapter; current Darwin does
not support successful executable pin creation.
