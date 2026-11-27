# `simple run` cannot interpret a program that imports the compiler frontend (native CLI, Windows)

Status: open
Found: 2026-11-23, unit_range_cast_native_execution_blocked Lane 9 follow-up (worktree dz1)
Binary: `C:/dev/wt/dz1/build/dz1/cli_main.exe`, the pure-Simple native CLI built from release/1.0.0 plus #11012 (sha256 `9b6c75f516cc648b923dfb88f6a65ccf83e6bf018e9f31323e47d50f6c2dd231`). The older nv2 CLI (`ea78bedd…`) shows the same `binary operator not implemented`.
Env: llvm-mingw UCRT `bin` first on PATH. Each run compiles about 645 modules before interpreting, which takes about 13 minutes.

## Repro (each file under `src/app/<dir>/`, run with `cli_main.exe run <file>`)

m6, which fails with `Interpret error in app.<dir>.m6: binary operator not implemented` (rc 1, prints nothing, not even `parsed`):

    use compiler.common.config.{Logger}
    use compiler.frontend.frontend.{parse_full_frontend}
    use compiler.hir.hir_lowering.types.{HirLowering}
    use compiler.hir.hir_lowering.items.*

    fn main():
        val src = "unit Dist: i64 as dd\n\nfn ratio(a: Dist, b: Dist) -> i64:\n    a / b\n"
        val module = parse_full_frontend(src, "p.spl", "p.spl", Logger(level: 0))
        print "parsed"
        var hir_lowering = HirLowering.with_filename("p.spl")
        val hir = hir_lowering.lower_module(module)
        print "hir"

m5 is the same without the two `hir_lowering` imports and the HIR lines. It fails earlier, with `unresolved method call: len (receiver kind nil) at src/lib/nogc_sync_mut/sffi/runtime.spl:168:15`. That is `xxh3_128_text`, where `hex.len()` is called on the result of the extern `rt_xxh3_128_text(data)`, which came back nil in the interpreter. This looks like the unbacked-extern-returns-nil class (`unregistered_extern_silent_nil_2026-08-01.md`).

The full MIR-dump probe (the m6 imports plus `compiler.mir.*` and `MirLowering`) gives the same `binary operator not implemented`.

## Controls (same binary)
- Plain structs, loops and text `+` work. `m1` prints `HIR_ERROR:x` with rc 0, and `m3` (an extern declaration plus text concatenation) returns rc 0.
- `for v in d.values()` on a dict literal fails with `unresolved method call: values (receiver kind dict)`. This is a separate interpreter gap, recorded here and not investigated.

## Notes
- The error text comes from `src/compiler/70.backend/backend/interpreter_binop.spl:290` (the fall-through arm). The operator and operand kinds are not reported, so the message cannot be localised. A first fix is to include the op and the operand value kinds in the error.
- Workaround: run such probes as specs with the Rust seed. `C:/dev/wt/sd1-target/release/simple.exe test test/01_unit/compiler/mir/unit_div_remainder_native_spec.spl` passes 8/8.
- Infra note: with C: at 2.2 GB free, `run` failed earlier with `SCV-E-ADMISSION: snapshot-materialize-failed` / `-digest` (on a different file each time). After freeing about 3 GB it went away. That is disk exhaustion, not this bug.
