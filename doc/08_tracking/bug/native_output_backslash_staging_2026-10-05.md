# Windows native output paths are incorrectly staged under the current directory

The new Phase2 compiler passed HIR/MIR on native_declared_enum_constructor,
but lld-link rejected an output beginning `./C:\\Users\\...`. The focused
regression harness supplied a valid Windows absolute path with backslashes.
Both compile_targets and build_intermediate_policy searched only for `/`,
so the entire absolute path became the output filename under parent `.`.

Use one host-aware parent/name policy for staging and cleanup. On Windows,
normalize separators before splitting; on Unix preserve literal backslashes.
Retain drive roots, Unix root and UNC parents. The CLI now uses the same
parent function as stale-intermediate cleanup, preserving sibling staging and
the existing rule that a failed build leaves the requested output untouched.

Three executable scenarios cover Windows mixed separators/spaces, root/UNC
paths, and Unix literal filenames. Native execution is UNRUN. Harness-only
forward-slash normalization is a temporary workaround, not proof of this fix.
