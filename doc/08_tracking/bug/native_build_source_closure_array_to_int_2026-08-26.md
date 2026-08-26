# Native build source closure reports locationless array-to-int conversion

## Status

Open bootstrap blocker. The current no-stub pure-Simple CLI build reaches the
source-closure inventory and then exits with only:

`error: semantic: type mismatch: cannot convert array to int`

The diagnostic does not identify the source file, expression, or call stack.

## Reproducer identity

- source revision base: `03432f5ea555ff73d772a40285ca77e2abb59ec2`
- Rust bootstrap compiler SHA-256:
  `ffb639cf56605bfaf719db4e456d410a22f90604c3bc9bf7fdc322b13ab36d9d`
- backend/profile: Cranelift, dynload, entry closure, no stub fallback
- entry: `src/app/cli/_CliMain/main_and_help.spl`
- focused shard: `--parse-shard=0/8`
- log: `build/native_probe/render-shard0-diagnostic2.log`

The shard resolves more than 320 closure files before the failure. The prior
`mission_critical/__init__.spl` Dedent parse defect is fixed and no longer
appears in this run.

## Required fix

The array-to-int conversion diagnostic must carry the source path and span (or
an interpreter call stack) so the owning Simple expression can be corrected.
The no-stub pure-Simple CLI must then build successfully before the rendering
guest or Vulkan capture is admissible.
