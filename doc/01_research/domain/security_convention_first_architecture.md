<!-- codex-research -->
# Security Convention-First Architecture Domain Research

Date: 2026-05-22

## References

- OWASP Authorization Cheat Sheet: https://cheatsheetseries.owasp.org/cheatsheets/Authorization_Cheat_Sheet.html
- Linux Landlock userspace API documentation: https://www.kernel.org/doc/html/v5.14/userspace-api/landlock.html
- WASI capability model notes: https://github.com/WebAssembly/WASI/blob/main/docs/Capabilities.md
- WASI overview: https://wasi.dev/
- FreeBSD Capsicum paper: https://papers.freebsd.org/2010/rwatson-capsicum/

## Findings

OWASP recommends least privilege, deny-by-default authorization, server-side checks, appropriate logging, and unit/integration tests for authorization logic. This supports Simple's default-deny feature boundaries, mandatory gates, and compiler-generated diagnostics.

Landlock is designed to restrict ambient process rights, especially filesystem access, without requiring privileged setup. This supports Simple's sandbox policy as a high-level manifest that can lower to Landlock on Linux while preserving the same language-level contract.

WASI documents capabilities as explicit authorities; filesystem-style access is represented through handles rather than unrestricted global paths. This supports Simple's native object-capability handles (`ReadFile`, `WriteFile`, `NetworkEndpoint`, `EnvVar`, `ProcessSpawner`) replacing ambient APIs.

Capsicum provides a Unix capability/sandbox model using capability mode and capabilities while extending existing APIs. This supports the Simple plan's FreeBSD/Simple OS direction and reinforces the idea that ambient authority should be removed at sandbox boundaries.

## Domain Implications for Simple

- Security defaults should be fail-closed: missing rules deny privileged crossings rather than permit them.
- Authorization should be centralized at gates/security roots, not scattered through service code.
- UI permission checks should be treated as observations only; server-side gates remain authoritative.
- Sandboxed code should receive explicit handles and manifests, not global filesystem/network/env authority.
- Generated artifacts should be auditable because authorization errors are often structural and architectural, not just local runtime bugs.

## 2026-05-23 Backend Isolation Follow-up

- Current Linux Landlock userspace documentation describes Landlock as an unprivileged access-control API that requires ABI detection and rights filtering for older kernels. This supports keeping Landlock filesystem enforcement as a backend-specific installer rather than assuming every Linux host supports the newest rights set.
- Current Linux seccomp filter documentation requires either `no_new_privs` or sufficient privilege before installing a BPF syscall filter. This supports Simple's Linux backend installing seccomp only after host setup, and testing it in forked children because the filter is irreversible for the current process.
- Current Linux Landlock documentation requires callers to detect the available ABI and only use supported access rights. This supports Simple's Linux backend filtering `REFER`, `TRUNCATE`, and device-ioctl rights before creating path-beneath filesystem rules.
- Current WASI documentation continues to frame runtime authority around explicit capabilities such as preopened directories and environment/stdio capabilities. This supports keeping WASI lowering tied to explicit host import/preopen tables rather than ambient module authority.
