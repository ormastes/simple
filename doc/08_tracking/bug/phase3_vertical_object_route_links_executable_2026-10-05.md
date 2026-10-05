# Phase3 vertical diagnostic accidentally requests executable linking

Status: command construction repaired; native requalification pending.

The Phase3 vertical collector exports `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1`
but its Phase2/3 command builder omitted `--emit-object`. The native-build
coordinator parses output kind from argv and replaces the inherited environment.
An output named `module.o` does not select a relocatable object.

Observed with producer `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`
and source `96eaa4da8783f56a3a7954399fbb83573e36afa4`:

- `src/app/cli/bootstrap_focused_native_build_args.spl` reached native compile,
  then failed executable linking with undefined `__simple_main`.
- `src/app/cli/bootstrap_identity.spl` completed native compile (1/1) before
  the same link error.

These are not evidence that either module failed HIR or MIR lowering. They
remain failed diagnostic tasks until actual object artifacts are validated.
The original run continues collecting all other entries without modification.

Repair: pass `--emit-object` explicitly in the shared Phase C module builder.
Preserve the existing environment binding for the direct driver, backend
selection, resource budgets, cache identities and object-container validation.
The command contract covers both backends, spaces in paths and an empty inherited
output-mode environment. It passed on Windows via Git Bash. This shell test
does not prove native compilation or linking.

Native probe: `windows-restart-20261004/p3-explicit-object-probe20-1`, two
completed entries above, isolated outputs and their closed existing caches.
Request SHA256: `15f22727cbe8b55d9cec773d62f772882adafd87b549257103fa374e1ec7b707`.
No cache stamp rewriting; no success is inferred from a cache directory.
