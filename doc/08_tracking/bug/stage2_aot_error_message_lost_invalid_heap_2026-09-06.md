# Stage-2 AOT compile error reports `<invalid-heap:0x…>` instead of its message

- **Date:** 2026-09-06
- **Status:** OPEN
- **Severity:** release-blocking (fails the staged bootstrap at `failure_root=stage2`)
- **Area:** `src/compiler/80.driver/driver_aot_native_output.spl`, native AOT lane

## Symptom

The Stage-2 compiler cannot native-build a three-line hello world:

```sh
cd /home/yoon/bootstrap-wt
T=$(mktemp -d); printf 'fn main() -> i64:\n    print "hello"\n    0\n' > $T/hw.spl
build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple native-build $T/hw.spl -o $T/hw
```

```
reason: AOT compile error in <unit>: <invalid-heap:0xc4b8e01>
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
```

Exit 1. Reproduced 2026-09-06 (address differs per run: `0xd76b541`, `0xc4b8e01`
— it is a live heap address, so the value is tag-`TAG_HEAP` pointing at
something that is not a text object).

## What is actually broken here

`<invalid-heap:0x…>` is **the error message itself**, not the error. The message
is produced at `src/compiler/80.driver/driver_aot_native_output.spl:1552`:

```
    match compiled:
        case Err(err):
            return Err("AOT compile error in {name}: {err.to_text()}")
```

`compiled` is the `Result` returned by `session.compile_aot_module(...)` /
`compile_module_with_backend_target_cpu_storage_bindings(...)` a few lines
above. Its `Err` payload does not survive the crossing on the stage-2 native
lane: `err.to_text()` renders a misdecoded tagged value.

So the AOT backend **did** fail for some real reason, and the diagnostic that
would name it is destroyed on the way out. Every downstream consumer — the build
outcome summary, `scripts/check/check-stage2-hello-world-native-build.shs`, the
bootstrap `failure_root` — only ever sees `<invalid-heap:0x…>`.

**Fix the message plumbing first.** Until the `Err` payload survives, the
underlying codegen defect cannot be named, and any attempt to guess it is
guessing.

## Relationship to the restored `_MirToLlvm` guards

Investigated while restoring the four correctness guards `cb1e4981701` deleted
from `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
(`first_unemitted_call_destination`, discriminant-based `Call` dispatch + its
emitted-destination panic, the `defined_locals` emission receipt, and the
float→`ptr` return-mismatch panic).

**None of the four is confirmed to fire here, and none is ruled out.** The
guards `panic()`, which bypasses this lossy `Result` path entirely, so if one of
them were firing in stage 2 the operator would see its located message, not
`<invalid-heap:…>`. That is an argument that the *current* stage-2 failure is
something else — but the stage-2 binary at the path above predates the
restoration, so it contains none of the guards. Confirming or excluding them
requires a stage-2 rebuilt from a tree that carries them.

Probes attempted:

- **Interpreted pure-Simple lane** (`bin/simple run src/app/cli/bootstrap_main.spl
  native-build hw.spl`, seed interpreter, guards live): fails EARLIER and
  differently — `native-capsule-receipt-invalid:<unit>` — and never reaches the
  LLVM text backend. Not a valid probe for this defect. No guard panic appears
  in its 1,465-line log.
- **Rebuilding stage 2 with the guards:** not attempted; it is a full bootstrap
  and one is already running on this host.

## Evidence limits

`bin/simple` on this host is the Rust seed and no runnable pure-Simple full CLI
is deployed, so all evidence above is seed-produced or produced by an
already-built stage-2 binary. No bootstrap was run for this record.

## Next steps

1. Make the `Err` payload of `compile_aot_module` survive to
   `driver_aot_native_output.spl:1552` (or capture the message eagerly at the
   raising site) so the real AOT error is nameable.
2. Re-run the reproducer, record the now-visible message.
3. Only then decide whether the restored `_MirToLlvm` guards are relevant.
