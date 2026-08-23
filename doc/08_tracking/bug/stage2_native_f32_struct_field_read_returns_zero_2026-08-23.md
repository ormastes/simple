# stage-2 native codegen reads every f32 struct field as 0.0

- **Filed:** 2026-08-23
- **Severity:** high — silent wrong data, no crash and no diagnostic
- **Class:** engine divergence (stage-2 pure-Simple native codegen vs Rust seed interpreter)
- **Status:** OPEN — reproduced and pinned by a spec; fix not landed
- **Reproduce spec:** `test/01_unit/compiler/backend/f32_struct_field_read_spec.spl`

## Artifact under test

| | |
|---|---|
| binary | stage-2 bootstrap compiler, copied to `lane/bin/stage2` |
| origin | `hircodec-1/build/phase_snapshots/phase1_1787475451_phase2_1787476227/simple` |
| size / mtime | 132931640, 2026-08-23 09:09:40 +0000 |
| md5 | `fa160e5b680ebb0288a84b1d42231cc3` |
| `--version` | `simple-bootstrap 1.0.0-RC` |

Stage binaries are the BOOTSTRAP cli (`src/app/cli/bootstrap_main.spl`): only
`compile`, `native-build`, `--version`, `--help`. There is no `test` command,
so specs are driven as `native-build <spec> -o <bin> && <bin>`.

## Symptom

```
struct P4:
    x: f32
    y: f32
    z: f32
    w: f32

val a = P4(x: 1.0f32, y: 2.5f32, z: 3.0f32, w: 4.0f32)
print a.x      # 0.0   expected 1.0
print a.y      # 0.0   expected 2.5
print a.w      # 0.0   expected 4.0
```

Built with
`stage2 native-build --entry f32r.spl -o f32r --entry-closure --runtime-bundle auto`
(build rc 0), then run directly (run rc 0). Nothing crashes; the values are
simply zero.

## It is a divergence, not a shared defect

Measured 2026-08-23, same source file, three cells:

| engine | result |
|---|---|
| stage-2 pure-Simple, native codegen | `0.0 / 0.0 / 0.0` **WRONG** |
| Rust seed interpreter (`seed run`) | `1.0 / 2.5 / 4.0` correct |
| Rust seed, native codegen | **unavailable** — see below |

The seed binary in use (`bin/release/x86_64-unknown-linux-gnu/simple`, md5
`8773f4cc1c67…`, 60650360 bytes, 2026-08-23 10:01) cannot native-build current
`src/`: it stops at `error: semantic: unknown extern function:
rt_heap_ref_wellformed`. So the third cell — is this native codegen in general,
or the pure-Simple backend specifically? — is **not yet answered**, and is the
first thing the next session should settle. Do not assume either way.

Per the twin rule: the defect is present in pure Simple and **verified absent
in the Rust seed interpreter**, with the evidence above.

## It is specific to f32

The identical file with every `f32` replaced by `f64` prints `1.0 / 2.5 / 4.0`
correctly on stage-2 native. So this is neither a general struct-field defect
nor a general floating-point defect. The `f64` control is carried in the
reproduce spec as a passing example precisely so a regression in the wider
struct-field path cannot be mistaken for this bug.

## Root cause (from the object code)

The constructor **stores** an `f32` field as a raw IEEE-754 **double** bit
pattern occupying the full 8-byte slot — `1.0f32` is stored as
`0x3FF0000000000000`, and `0.1f32` is stored as f64 `0x3fb999999999999a`, i.e.
*not* the f32-widened `0x3fb99999a0000000`.

The field **read** emits `vcvttss2si (%rbx),%rdi` against that same slot. That
single instruction is wrong twice over:

1. `ss` = scalar **single** — it loads 4 bytes where the value occupies 8.
2. `cvtt…si` = convert-with-truncation to **signed integer** — a float load was
   required, not an int conversion.

The low 4 bytes of an f64 bit pattern are ~0 for ordinary magnitudes, so every
`f32` field reads back `0.0`. Store and read disagree on both width and
operation; the store convention is the one the C runtime and the interpreter
already agree with, so the read is the side that should change.

## Blast radius

Any code that round-trips an f32 through a struct field computes on zeros,
silently. `src/lib/nogc_sync_mut/simd.spl` is built entirely on `f32`-field
vector structs (`Vec4f{x,y,z,w}`), so the whole SIMD surface is affected once
its runtime symbols exist (see the companion finding below).

## Companion finding — 67 unresolved runtime symbols

Separately and independently, native-building any spec whose import closure
reaches `std.simd` fails at link with 67 undefined runtime symbols (54
`rt_simd_*` lane ops plus `rt_mmap`/`rt_munmap`/`rt_madvise`/`rt_msync`,
`rt_file_stat`/`rt_file_lock`/`rt_file_unlock`/`rt_file_mmap_read_{bytes,text}`,
`rt_string_index_of`, `rt_black_box`, `rt_is_debug_mode_enabled`,
`rt_unwrap_or_trap`). These are implemented only in the Rust seed interpreter
(`src/compiler_rust/compiler/src/interpreter_extern/simd.rs`) and are absent
from the C runtime. Notes:

- `rt_unwrap_or_trap` is the exact symbol from the 2026-08-21 stage-binary SEGV
  incident (`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`)
  and is **still undefined in the C runtime**, so that incident's runtime half
  is not closed.
- `rt_unwrap_or_trap`, `rt_file_stat` and `rt_string_index_of` *are* defined in
  `src/runtime/simple_core/*.spl`, but the pure-Simple `simple-core` archive
  route is closed for stage2: `stage2` has no `--emit-archive`, so
  `check-simple-core-runtime-smoke.shs` reports
  `error=selected_simple_binary_lacks_emit_archive`. `--runtime-bundle auto`
  therefore falls back to the C runtime, which lacks them.
- The edge that drags `simd.spl` into an unrelated spec's closure is
  package-barrel over-pull: `src/lib/nogc_sync_mut/__init__.spl` is a 399-line
  re-export barrel covering 34 siblings including `simd.spl` (lines 358-366),
  and a glob import pulls every sibling. Filed here as context only — do NOT
  "fix" this by trimming std's import graph; that changes closure semantics for
  every consumer.

## Evidence of discrimination

The reproduce spec is not a spec that would pass either way:

| engine | result |
|---|---|
| stage-2 native | `7 examples, 6 failures` — every f32 example fails, the f64 control passes |
| seed interpreter | `7 examples, 0 failures`, `executed=7` |

## Next steps

1. Settle the missing third cell (seed native codegen) with a seed new enough to
   build current `src/`.
2. Fix the read side to mirror the f64 field-read path.
3. Re-run the reproduce spec on a rebuilt stage2 — the fix cannot be verified
   without a bootstrap, since stage2 is already compiled.
