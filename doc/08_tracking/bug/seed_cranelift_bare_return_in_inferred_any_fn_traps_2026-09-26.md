# Stage 2 admission SIGILL: seed cranelift lowers a bare `return` in an inferred-`ANY` function to `ud2`

- **Filed:** 2026-09-26
- **Status:** FIXED in the seed (`src/compiler_rust/compiler/src/codegen/instr/body.rs`);
  Stage 2 lane result recorded at the end of this record.
- **Area:** Rust seed, cranelift backend, `Terminator::Return(None)` lowering
- **Host:** yoon-note, x86_64-unknown-linux-gnu, 7.4 GiB RAM
- **Supersedes the framing in:**
  `stage2_candidate_env_lexer_array_oob_sigill_2026-09-26.md` (the array is
  not empty — see below) and the "environment-specific" / "4 GB memory growth"
  framing at the end of
  `stage2_candidate_env_get_infinite_recursion_sigill_2026-09-26.md`.

## Symptom

`run-phase1-local.shs --stop-after-stage2` aborts with
`candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)`.
The probe's captured log ends at `[build] phase=parse ... elapsed_ms=48` with no
diagnostic; every superseded sanity record from today (14:19 through 16:04)
carries `frontend_smoke_status=132`.

## What was actually measured (all under `run_capped.shs`, `CAP_MEM_MAX=4G`)

| invocation | binary | wall | max RSS | rc |
|---|---|---|---|---|
| exact probe command, sanitized env, `setsid` | `stage2/x86_64-unknown-linux-gnu/simple.rejected` (sha `bb88b5…`, the real candidate) | 0.24 s | **47 MB** | **132** |
| same command | `stage3/.../stage2-runtime-authority/simple` (sha `7f95a4…` = the Rust seed) | 58.7 s | **4.0 GB** (tree peak 4.8 GB) | 1 (`SCV-E-SNAPSHOT`, no `SIMPLE_SCV_FREEZE_FALLBACK`) |
| 14-way env/flag bisect of the probe on the real candidate (`SIMPLE_BOOTSTRAP` 0/1, ±`SCV_FREEZE_FALLBACK`, ±`--entry-closure`, ±`--mode one-binary`, ±`--runtime-bundle`, ±`--backend`, ±`SIMPLE_FRONTEND_DELEGATED`, ±`FORCE_WORKER`, ±`SIMPLE_LIB`, ±`COLD_INIT`, ±`NO_STUB_FALLBACK`, the record's "standalone" command, bare flags) | real candidate | 0.24 s each | 47 MB each | **132 every time** |
| the record's "standalone rc=0" command in an unsanitized shell | real candidate | 0.24 s | 47 MB | 132 |

Conclusions:

- **The 4 GB claim is refuted for the candidate.** `stage2-runtime-authority/simple`
  is byte-identical to `src/compiler_rust/target/bootstrap/simple`; it is the
  seed that *built* Stage 2, not the Stage 2 output. The previous lane ran the
  seed, which interprets `src/app/cli/native_build_main.spl` and the whole
  compiler closure from source (RSS ramps ~90 MB/s to 4.0 GB in ~35 s, then
  plateaus). The real candidate peaks at 47 MB.
- **rc=132 is not memory-related and not environment-specific.** It reproduces
  in 0.24 s in every configuration, including the developer's unsanitized shell.
  The "rc=0 standalone" row in the earlier record was the seed, not the candidate.

## Root cause (gdb + objdump on the real candidate)

Backtrace is the known one (`current_core_lexer_save` <- `lex_next` <-
`lex_next_snapshot` <- `parser_advance` <- `parser_init_with_path`). But the
array is **not empty**: a hardware watchpoint on the module slot
`compiler__frontend__core__lexer__lex_env_save_enabled` (0x18c8a81) fires once,
from `__module_init_compiler__frontend__core__lexer` via
`__simple_call_module_inits`, and the pointed-to object stays
`len=1 cap=4` through `lex_init_with_path`, `lex_next` and the trap. The
function has exactly one `ud2`, reached by
`call rt_value_unbox_int; test rax,rax; je ud2` — i.e. the **`return` branch**
of `if not lex_env_save_enabled[0]: return` was lowered to a trap.

Ten-line reproducer, compiled with the seed exactly as Stage 2 compiles
(`SIMPLE_NATIVE_BUILD_RUST=1 … --backend cranelift --runtime-bundle
core-c-bootstrap --mode one-binary`), 3 s / 115 MB, SIGILLs on run:

```
fn save(b: bool, x: i64):
    if not b:
        return
    print("enabled {x}")
```

Shape matrix (all built the same way): traps when the function has **no
declared return type**, its **tail statement is a value-producing expression**
(a call — `print`, a user unit fn, `env_set -> bool` — or `x + 1`), and it
contains a **bare `return`**. Does not trap with `-> unit`, with a non-value
tail (`var y = …`), with a trailing explicit `return`, or as `if/else`. The
09-19 seed (`bin/simple`) traps identically; the shape is not knob- or
backend-flag-dependent (`SIMPLE_BOOTSTRAP` 0/1, bundle, one-binary, entry
closure all irrelevant). MIR is correct (`bb1: Return(None)`); the defect is
in codegen:

- `hir/lower/module_lowering/function.rs:1081-1086` (since `da8964fe990`,
  2026-09-16): an undeclared-return function whose `body_produces_value` is
  typed `TypeId::ANY`.
- `codegen/instr/body.rs` `Terminator::Return(None)` arm: handled only
  `generator` and `return_type == VOID`; everything else hit the fail-fast
  `trap(unwrap_user(1))` (there since Feb 2026, and already documented for the
  `-> ()` spelling in `type_resolver.rs:413-432`).

So since 2026-09-16 every natively-compiled `fn f(…): if c: return; <call>` traps
on its early return, and `current_core_lexer_save` (this shape since
2026-08-08) is executed on the first token of the first file.

## Fix

`src/compiler_rust/compiler/src/codegen/instr/body.rs`: a `Return(None)` in a
function whose return type is `TypeId::ANY` returns the tagged nil constant
`3` (`TAG_SPECIAL=0b011 | SPECIAL_NIL=0`, the same encoding `helpers.rs`,
`pattern.rs` and `calls.rs` already emit); the trap arm is kept for genuinely
declared non-nil return types. `cargo check --release --bin simple` clean.

A first cut of this fix called `runtime_funcs["rt_value_nil"]` like the
generator arm does. That panicked (`no entry found for key`, exit 134) inside
the Stage 2 build, because the AOT `ObjectModule` backend does not register
that key in `runtime_funcs` — the generator arm only ever runs under the JIT.
Measured on the lane at 17:18; replaced by the constant above.

Verification with the 10-line reproducer and the specs below is by the Stage 2
lane's rebuilt seed (the working-tree `target/bootstrap` is frozen read-only by
the lane, deliberately).

## Specs

- `test/01_unit/compiler/backend/bare_return_in_inferred_any_fn_spec.spl` —
  reproducing: native-builds the lexer-shaped fixture through `bin/simple`
  and asserts the executable's transcript and exit status. On the unfixed seed:
  `outcome=ERROR executed=1 failed=1` (`assert_equal failed: expected ok, got`),
  `process_run` reports `-1` for the SIGILL-killed child.
- `test/01_unit/compiler/backend/bare_return_shapes_inferred_any_fn_spec.spl` —
  generalization: one fixture with the while-loop, nested-if, else-arm and
  multi-return shapes plus the never-affected `-> unit` / non-value-tail forms;
  asserts the full transcript. Unfixed: `executed=1 failed=1`.

An in-spec function cannot reproduce this: the sspec runner interprets spec
modules (measured — such a spec passes on the unfixed seed), which is why both
specs native-build a fixture instead.

## Related, still open (not fixed here)

- `stage2_candidate_env_lexer_array_oob_sigill_2026-09-26.md`'s guard
  (`lex_env_save_on()`) is harmless but was not the cause; its "unbounded
  memory" section describes the seed, not the candidate.
- Any other `Return(None)` reaching the trap arm with a declared non-VOID,
  non-ANY type is still a fail-fast trap by design; the frontend should reject
  a bare `return` there instead.
