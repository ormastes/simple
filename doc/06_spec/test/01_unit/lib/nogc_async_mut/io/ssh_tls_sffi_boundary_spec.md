# SSH/TLS SFFI Boundary Specification - nogc_async_mut

Executable spec:

- `test/01_unit/lib/nogc_async_mut/io/ssh_tls_sffi_boundary_spec.spl`

## Scenarios

- Async SSH SFFI facade re-exports native protocol bypass classification.
- Async TLS server SFFI facade re-exports native protocol bypass classification.

## Evidence

```text
bin/simple test test/01_unit/lib/nogc_async_mut/io/ssh_tls_sffi_boundary_spec.spl --mode=interpreter
Passed: 2
Failed: 0
```
