# Compiler host nullable environment reads

The compiler host environment facade preserves the raw nullable result of an environment lookup. The executable spec is [`compiler_host_nullable_env_get_spec.spl`](../../../../../test/01_unit/compiler/driver/compiler_host_nullable_env_get_spec.spl).

- An unset variable yields `nil`.
- An explicitly empty variable yields a present empty string.
- A populated variable yields its exact text.

The spec saves and restores the test variable. It covers the facade contract used by compiler driver environment reads; compiler-wide runtime execution remains subject to the Mac bootstrap admission gate.
