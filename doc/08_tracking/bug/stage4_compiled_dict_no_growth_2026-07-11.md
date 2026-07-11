# Stage-4 compiled in-process paths broken: RuntimeDict never grows (root cause) + Cranelift Host→x86-64 leak

**Date:** 2026-07-11 · **Status:** both fixes implemented; seed/runtime rebuild + stage-4 redeploy required
**Symptoms fixed by this:** deployed `bin/simple native-build …` traps instantly
("runtime error: field access on nil receiver", exit 132 in `SymbolTable.lookup`);
`bin/simple check` (native, non-delegated) exits 3 with zero output; every compiled
dict-heavy path unreliable — the concrete reason day-to-day commands still delegate
to the seed.

## Root cause 1 — Rust `RuntimeDict` was fixed-capacity; full-table inserts silently dropped

`src/compiler_rust/runtime/src/value/dict.rs`: `RuntimeDict` stored its slots INLINE
after the header, so the table could never grow. `rt_dict_set` on a full table returned
`false // Dict is full` — and compiled Simple code ignores that bool. Every compiled
`{}` dict starts at capacity 8 (`rt_dict_new` clamps to a minimum of 8), so the **9th
insert into any compiled dict was silently dropped**. Interpreted runs use Rust
`HashMap` (unbounded) — which is why everything works when delegated to the seed and
breaks in-process in the stage-4 binary.

### Debug chain (lldb on the deployed binary, symbols present)

1. Trap at `hir__hir_types__SymbolTable_dot_lookup+1860` = codegen nil-receiver guard
   after `val scope = self.scopes[scope_id.id]` returned nil.
2. Logged every `rt_index_get` at that site: calls with key `0x0` (Int 0, root scope)
   succeed; the failing call asks for key `0x58` = **Int(11)** — scope id 11 was never
   in the dict.
3. `push_scope` had executed 11 times: `next_scope_id`/`current_scope` (plain struct
   fields) advanced to 11, but `self.scopes[raw_id] = Scope(...)` → `rt_dict_set`
   started returning false once the 8 slots filled. Verified in-process:
   `rt_dict_set(dict, 0, scope)` → true, `rt_dict_len` = 1, get-after-set fine —
   the table only breaks at the capacity wall.
4. RuntimeValue encoding sanity (for future debugging): TAG_INT=0b000 (raw 0 IS
   Int(0), a legal dict key), NIL = 0x3 (TAG_SPECIAL|payload 0), heap ptrs tagged
   low-bit 1. The nil-receiver guard normalizes NIL→0 before `cbnz`.

### Fix

`dict.rs`: slot storage moved to a separate allocation (`data: *mut RuntimeValue`);
`rt_dict_set` grows (×2, rehash) at ≥3/4 load so an insert can never hit a full
table. `rt_dict_new/free/get/clear/keys/values/entries/remove` updated for the
indirect layout. No consumer outside dict.rs touched the inline layout (verified by
grep over runtime+compiler+driver+common crates). Regression test
`test_dict_grows_past_initial_capacity` (100 inserts into a default dict, then
removal across the grown table). `cargo test -p simple-runtime`: 706 value-tests
pass; only pre-existing failures remain (aes known-answer ×2, executor ×2, loader
×2 — all reproduce on pristine HEAD).

The C runtime twin (`src/runtime/runtime_native.c`, `RtCoreDict`) already grows —
only the Rust runtime had the defect.

## Root cause 2 — pure-Simple Cranelift adapter maps `Host` target to x86-64

`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
`codegen_target_to_cl()` had `case Host: CL_TARGET_X86_64`, so seed-interpreted
native-builds emitted **x86_64-unknown-linux-gnu ELF objects on arm64 macs** for the
entry module (`ld: unknown file type`). Same bug class as the llvm_target.spl Host
CPU-string leak fixed 2026-07-10. Fixed: `Host` (and the default arm) now resolve via
`host_arch()`. Verified: repro rebuild emits `Mach-O 64-bit object arm64`.

## Not fixed here (observed while reproducing, filed for follow-up)

- **Duplicate `_main` (20 symbols) at link** when native-building a standalone entry
  file directly: the per-module object AND the synthetic `simple_entry.o` both define
  the entry symbols. Bootstrap entries built via `bootstrap-from-scratch.sh` don't
  hit this lane.
- **Cranelift verifier error** compiling `compiler.common.diagnostics.span::is_method`
  ("AOT define_function error: Verifier errors") when the entry closure pulls
  `src/compiler` — blocks a minimal SymbolTable repro binary; unrelated to the dict fix.

## Deployment

The deployed stage-4 binary links the OLD runtime archive; the dict fix reaches
`bin/simple` only via seed/runtime rebuild (`cargo … --profile bootstrap -p
simple-driver / -p simple-native-all --features llvm`) + stage-4 rebuild + redeploy.
After redeploy, re-test: `bin/simple native-build …` (SymbolTable wall), native
`check` exit-3, and whether test/check delegation can begin to retire.

## 15:09 redeploy attempt: dict fix NECESSARY but NOT SUFFICIENT — rolled back

A stage-4 binary built from source with all fixes (dict growth, Host triple,
`__simple_main`, parse normalizations, StringBuilder dedup) deployed at 15:09 and
FAILED the matrix:

- `run` / `-c`: exit 0 but ALL print output lost (1 byte written) — a worse
  regression than the 11:02 binary (which delegates run to the seed sibling).
- `check` (native, delegation retired in that build): still silent exit 3.
- `--version`, `test` (seed-delegated by design): pass.

Rolled back to the 11:02 binary (scratchpad simple.jul11.bak → bin/release);
restore verified (run prints, check green, cli_parser spec passes). The
check/lint delegation retirement (5d64ffc2) was surgically reverted on top of
origin (preserving peer commit 8a47830799's cli_ops changes) — retire again only
after a deployed binary passes the native-path matrix.

Conclusion: beyond RuntimeDict, the compiled full CLI has at least one more
in-process correctness wall (print/output path loses writes; check crashes
pre-output). The morning redeploy-gate failures (val-scalar,
struct-copy-isolation, class-in-array-mutation, cfg-arch-dispatch-b) remain the
best breadcrumbs — same class: compiled-code semantics diverging from
interpreted. Next probe: build a tiny compiled binary via the SAME stage-4
pipeline that only prints, then bisect print loss (rt_print* linkage vs lowering).

Build walls cleared to get this far (all landed):
1. self-hosted parser dedent-continuation (4 sites normalized + bug filed
   `self_hosted_parser_dedent_continuation_2026-07-11.md`);
2. duplicate module `common.string_builder` from src/app+src/lib source roots
   (peer twin deleted, 4 imports retargeted to the lib canonical).
