# `simple compile --format=smf` crashes on nil receiver (2026-07-31)

**Found by:** link_manager Lane SMFMAP scout while verifying the byte-parity
harness for Phase 1.
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

```
bin/simple compile --format=smf -o out.smf examples/01_getting_started/hello_native.spl
runtime error: field access on nil receiver
exit 132 (core dump)
```

Path: `src/app/cli/bootstrap_main.spl:318 run_compile_bootstrap`.

The simplest SMF-output command is therefore unusable; the working
alternative (and what the link_manager parity harness uses instead) is:

```
bin/simple native-build --entry examples/01_getting_started/hello_native.spl \
  -o <out> --entry-closure --runtime-bundle auto
```

which is deterministic (two runs byte-identical, sha256
`b9f37a50a84d2d6601c98b9e8ac3ddce814d7cfb275a5aa7683f416e9bc86121`, 23384 B)
but routes final link through the external `clang` fallback, so it exercises
the cc path rather than the in-repo SMF writer.

## Impact on LINK lane

Phase 1 acceptance ("byte-identical SMF output") needs a working in-repo SMF
emission command as its oracle input; until this crash is fixed the parity
harness can only cover the native-build/cc route. See
`.spipe/link_manager/smf_linker_map.md` §5–§6 for the full harness plan and
risk list.
