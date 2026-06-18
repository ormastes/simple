# SSH/TLS SFFI Boundary Specification - nogc_sync_mut

Executable spec:

- `test/01_unit/lib/nogc_sync_mut/io/ssh_tls_sffi_boundary_spec.spl`

## Scenarios

- SSH SFFI is classified as `native-protocol-bypass`, is not release allowed,
  and explains that release mode must use Simple SSH protocol modules.
- TLS server SFFI is classified as `native-protocol-bypass`, is not release
  allowed, and explains that release mode must use Simple TLS/HTTP protocol
  modules.

## Evidence

```text
bin/simple test test/01_unit/lib/nogc_sync_mut/io/ssh_tls_sffi_boundary_spec.spl --mode=interpreter
Passed: 2
Failed: 0
```
