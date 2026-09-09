# Chromium primitive oracle: canonical admission plan

Status: prepared, not admitted. This note records the exact post-admission
build and evidence gates. It does not authorize use of a rejected candidate.

## Canonical build

Run from the repository root only after a pure-Simple compiler has a valid
Stage-2 admission and the source/runtime snapshots are unchanged:

```text
sh scripts/check/build-chromium-primitive-oracle.shs \
  --bootstrap-output=build/bootstrap \
  --output=build/chromium-primitive-oracle/libsimple_chromium_primitive_oracle.dylib
```

The builder accepts exactly
`build/bootstrap/stage3/<host-triple>/stage2-admitted/simple`, verifies the
Stage-2 admission and parent sanity/provenance receipts plus the Stage-3
provenance/authority map. It replays the producer's complete Stage-2 admission
verifier and recomputes current source, Git, runtime, and tool authorities. It
refuses symlinks, `simple.rejected`, a noncanonical version identity, stale
hashes, fabricated/incomplete receipts, and missing evidence. It does not fall
back to `bin/simple` or the Rust seed.

The actual producer command, run only after all preflight gates pass, is:

```text
<stage3>/<host-triple>/stage2-admitted/simple native-build \
  --emit-shared \
  --source tools/chromium-primitive-oracle \
  --entry-closure \
  --entry tools/chromium-primitive-oracle/chromium_primitive_oracle.spl \
  --backend=llvm --strip \
  --cache-dir=<fresh-private-cache> \
  --output=<fresh-temp>/libsimple_chromium_primitive_oracle.dylib
```

`--emit-shared` is the pure-Simple CLI contract. The earlier environment-only
form was invalid because the CLI resets that internal environment variable
from its parsed flags. The admitted compiler bytes are copied into the private
build directory and rehashed before execution, so replacement of the admitted
path cannot change the running build. The producer also executes with the exact
tool `PATH` captured by the admitted Stage-2 command transcript; it does not
validate one toolchain and then accidentally inherit another from the caller.

The fresh temporary artifact is checked before no-clobber hard-link publication
to the target. Existing artifacts and receipts are refused, never overwritten.
The builder writes a hash-bound receipt beside the dylib containing the
compiler, admission/provenance/source, command, output, and exported-symbol
hashes plus length-framed hashes of the exact executed argv/environment.
`--dry-run` performs all preflight checks and prints the producer command
shape without invoking a compiler or creating a library.

## Frozen ABI

The Mach-O dylib must export exactly these five public oracle ABI functions:

```text
simple_chromium_oracle_abi_version
simple_chromium_oracle_create
simple_chromium_oracle_run_json_into
simple_chromium_oracle_last_error_into
simple_chromium_oracle_destroy
```

Verify the host architecture with `lipo -archs`; then use `nm -gU`, normalize
Darwin's leading underscore, retain defined text symbols with the
`simple_chromium_oracle_` prefix, and reject extras, duplicates, or omissions.
Compiler/runtime globals outside that frozen prefix are not part of this ABI
set. Record `file` and SHA-256 in the evidence receipt.

## Provenance and runtime gates

- `stage2-sanity.receipt` and `stage2-provenance.receipt` both exist, pass,
  and hash the exact compiler used for this build.
- The compiler source snapshot, runtime snapshot, tool authority, and oracle
  source hash are stable before and after compilation.
- The dylib is linked by Apple `ld` for arm64 Mach-O; shared plugins use
  `-undefined dynamic_lookup` so the host owns the runtime ABI.
- The broker and npm lockfile hashes match the pinned Electron `42.5.0` /
  Chrome `148.0.7778.271` fixture.
- The live load/run/release gate passes, including ABI version, all five
  symbols, complete web input/GPU response evidence, and
  `device_origin_readback=false` for CPU capture evidence.

Until every gate passes, retain artifacts as diagnostic evidence only and do
not rename or promote them to the canonical dylib.

## Fresh-output cache continuation

The prior wrapper invocation reached the canonical bootstrap and was refused
with `stage2-sanity-error: stale-evidence-output-root`. Its old output contains
run-bound evidence that must be preserved.

`scripts/bootstrap/resume-stage2-from-cache.sh OUTPUT_DIR` now treats its
argument solely as a cache donor. It holds that output's canonical lock,
checks the existing transcript, and copies only `stage2-native-cache` to a
unique `build/stage2-resume.XXXXXX` output. Source-before, source-after, and
copied-cache manifests must match. The copy has independent writable files;
symlinks and special files are refused. No old runtime, compiler candidate,
sanity evidence, transcript, or admission receipt is transferred.

The wrapper then delegates to the canonical `--full-bootstrap
--stop-after-stage2` entrypoint. That entrypoint recomputes the Rust input
fingerprint, pins the current runtime authority, snapshots source and tools,
and performs its ordinary sanity and admission gates. A cloned object is only
a cache input and does not establish admission.

Behavioral regression:
`sh test/01_unit/scripts/bootstrap_resume_stage2_from_cache_contract_test.shs`
passes cache-copy equality, writable-file independence, old-evidence exclusion,
symlink refusal, missing-authority refusal, and owned-lock enforcement.

The single subsequent canonical attempt used `build/stage2-resume.bphEaB`:
all 883 Stage 2 files compiled and linked, but hello-world positional native
compilation crashed during sanity (`raw_status=139`, `reason=child-signal`).
See `stage2_fresh_cache_resume_hello_world_sigsegv_2026-09-08.md` for hashes and
exact logs. The compiler was preserved as `simple.rejected`; Chrome remains
blocked on compiler admission.
