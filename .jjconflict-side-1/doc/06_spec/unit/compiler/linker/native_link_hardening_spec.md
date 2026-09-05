# Native linker hardening (legacy unit path)

Mirror of `test/unit/compiler/linker/native_link_hardening_spec.spl`.

The executable SSpec checks ELF direct and C-compiler fallback unresolved-symbol flags, excludes those flags on non-ELF/Darwin paths, and verifies strict links disable duplicate forgiveness and fallback.

This narrower legacy-path suite provides policy-level assertions and does not execute native links across all platforms.
