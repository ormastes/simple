# Bootstrap LLVM Failure Debugging

Use this workflow when a native bootstrap fails during LLVM generation. Rust is
only the seed in this workflow: seed diagnostics may explain why generation
stopped, but success is proved only by the resulting pure-Simple compiler.

## Diagnose the earliest broken boundary

Classify the failure before changing a backend:

1. An incorrect resolved owner in HIR is a name-resolution/lowering defect.
2. A `GlobalLoad` without a declared source global in MIR is a semantic-lowering
   defect. Do not make LLVM invent or accept that global.
3. Textual IR rejected by `llvm-as` is malformed LLVM generation.
4. Bitcode rejected by `opt -passes=verify` is an LLVM validity defect.
5. Verified bitcode rejected by `llc` is a target/code-generation defect.

For a seed-assisted Stage 4 build, preserve failure artifacts without changing
the normal output path:

```bash
SIMPLE_LLVM_DIAGNOSTIC_DIR=build/bootstrap/llvm-diagnostics \
  <stage3-simple> native-build <the-existing-stage4-arguments>
```

On a seed LLVM failure this writes partial `.ll` and `.bc`, the MIR debug form,
and an error receipt. Partial artifacts may be intentionally invalid because
generation stopped at the first semantic error; replaying them makes that LLVM
boundary independently visible while the MIR and receipt explain the earlier
semantic boundary.

To preserve complete `.ll`, `.bc`, and MIR for every successfully generated
module as well, add `SIMPLE_LLVM_DIAGNOSTIC_MODE=all`. This mode intentionally
adds I/O and disk usage, so use the default failure-only mode for fast bootstrap
retries.

The primary pure-Simple diagnostic mode exercises the actual Simple LLVM text
backend and an explicit LLVM boundary:

```bash
SIMPLE_LLVM_BITCODE_DEBUG=1 SIMPLE_KEEP_LLVM_IR=1 \
  <pure-simple> native-build --backend llvm <the-existing-build-arguments>
```

For every module, pure Simple emits textual `.ll`, `llvm-as` assembles `.bc`,
`opt -passes=verify` checks the bitcode, and `llc` compiles that bitcode to an
object. The reported stage and retained paths distinguish a Simple text-emitter
bug from invalid LLVM bitcode or a target backend failure.

Replay complete text IR or bitcode independently:

```bash
sh scripts/check/replay-llvm-artifact.shs module.ll build/check/llvm-replay
sh scripts/check/replay-llvm-artifact.shs module.bc build/check/llvm-replay
```

The replay performs text-to-bitcode assembly when needed, LLVM verification,
and object generation. It reports the exact failing stage and retains generated
bitcode/object files. Never treat replay success as Stage 4 success: build the
pure-Simple executable, run its sanity command and essential-tool smoke, then
deploy that executable.
