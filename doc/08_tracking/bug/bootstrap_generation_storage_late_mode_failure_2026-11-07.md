# Bootstrap generation storage rejects incompatible modes before Cargo

An actual WSL bootstrap completed four Cargo components before generation
publication failed in `bootstrap_stage3_copy_seed_tuple`: the selected filesystem
reported `0555` after a requested `0500` executable or `0400` library freeze.
The generation destination is `src/compiler_rust/target/bootstrap.generations`,
which can differ from the configured Cargo cache and output filesystem.

`bootstrap_stage3_preflight_generation_storage` now probes fresh owned files in
that actual destination before the first Rust authority workspace preparation
and Cargo command. It checks the same host-Perl policy as the final tuple freeze:
exact modes on Unix, including WSL; the existing read-only exception on native
Windows/MSYS/Cygwin. It removes its probe and reports an actionable filesystem
error. It neither changes mounts nor weakens the final publication checks.
Cached/pure-Simple paths that do not prepare a Rust workspace remain unchanged.

Focused verification on 2026-11-07 used the production helper and extracted
workspace function. A POSIX filesystem preserved both requested modes and left
no probe. The real metadata-disabled `/mnt/d` filesystem reported `0555` instead
of `0500` and was rejected before a Cargo sentinel or HOME cleanup; an existing
HOME sentinel survived. The regression is wired into the Linux idiom-gates job;
the incompatible-filesystem case requires an explicit environment path and is
reported as skipped when unavailable. No Cargo rebuild, generation publication,
native Windows execution, compiler qualification, or application/performance
qualification was performed for this focused change.

The original failed publication and separate metadata-enabled recovery remain
independent evidence. This early probe is capability preflight, not an admission
receipt or a guarantee that filesystem permissions cannot later change.
