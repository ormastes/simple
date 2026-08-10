# Stage-3 self-host SIGSEGV — independent gdb reproduction confirms the `bytes()` → `PointerSize.bytes` hijack, not a new fault

- **ID:** stage3_selfhost_segv_bytes_hijack_confirmed_reproduction_2026-08-10
- **Status:** CONFIRMED RECURRENCE of
  `doc/08_tracking/bug/stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md`.
  Not a new defect. Root cause still unfixed in the Rust seed's LLVM backend
  (`src/compiler_rust/compiler/src/codegen/llvm/functions.rs` suffix scan).
- **Relation to the long-standing blocker:** this crash still sits entirely
  upstream of `doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
  (source-loading phase, before HIR/MIR run at all) — that bug's fault site
  remains **never executed**.

## What this task did

Per assignment, this was root-cause analysis only — no fix attempted.

1. Read the three prerequisite docs (fleet task list, the nil-receiver
   blocker with its SIXTH-campaign appendix, and the 2026-08-09 bytes-hijack
   doc).
2. Found an already-built, already-admitted Stage-2 binary from a prior
   pinned clean campaign at
   `/home/ormastes/dev/s3camp6-out/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`,
   built from `origin/main` commit `94b861249c5718dd3a58881f924ccb4b94036661`
   (`git -C /home/ormastes/dev/s3camp6 log -1` confirms). Its md5
   (`ff6cf832d4d03d50b73362724fc2dedf`) matches the one recorded in the
   nil-receiver bug's SIXTH-campaign entry, so this is the exact admitted
   artifact from that prior run — not a stale/different build.
3. Re-derived the exact Stage-3 invocation from the recorded
   `stage3-command.transcript` in that output tree (argv and every
   `explicit-env:` line), rather than trusting a paraphrase.
4. Ran that invocation directly under `gdb --batch -ex run -ex bt -ex "bt
   full" -ex "info registers" -ex "x/10i $pc-20"` (no core-dump dependency,
   per the task's stated preference) from `/home/ormastes/dev/s3camp6`
   (the recorded `cwd`), with `ulimit -c unlimited` set first.
5. Cross-checked the faulting frame's disassembly against the fault address
   and register state to rule out the documented "gdb misattributes a
   call-through-0/garbage-pointer crash to the nearest unrelated symbol"
   trap.

## Exact repro command

```sh
export SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_ARENA_DECLS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=2 \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  SIMPLE_RUNTIME_PATH=/home/ormastes/dev/s3camp6-out/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority \
  SIMPLE_BINARY=/home/ormastes/dev/s3camp6-out/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple \
  RUST_LOG=error LC_ALL=C LANG=C TMPDIR=/tmp/s3repro/tmp
ulimit -c unlimited
cd /home/ormastes/dev/s3camp6
gdb --batch -ex run -ex bt -ex "bt full" -ex "info registers" \
  -ex "x/10i \$pc-20" --args \
  /home/ormastes/dev/s3camp6-out/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple \
  native-build --target x86_64-unknown-linux-gnu --backend llvm \
  --runtime-bundle core-c-bootstrap --threads 2 \
  --cache-dir /tmp/s3repro/cache --mode dynload \
  --runtime-path /home/ormastes/dev/s3camp6-out/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority \
  -o /tmp/s3repro/simple src/app/cli/bootstrap_main.spl
```

Crashed in under a few seconds — reproduced without a full bootstrap replay.

## The real backtrace (verified, not misattributed)

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000004d9617 in compiler.frontend.core.interpreter.hashmap.hm_hash_text ()
#0  0x00000000004d9617 in compiler.frontend.core.interpreter.hashmap.hm_hash_text ()
#1  0x00000000007e1ac9 in compiler__driver__driver_source_loading___driver_text_bucket_set_has ()
#2  0x00000000007e8573 in compiler__driver__driver_source_pipeline_loading__CompilerDriver.load_sources_impl ()
#3  0x00000000007dc819 in compiler__driver__driver_orchestration__CompilerDriver.compile ()
#4  0x000000000049b86e in app.cli.bootstrap_main.run_native_build_bootstrap ()
#5  0x0000000000498637 in main ()
```

Registers at fault: `rax=0x8 rbx=0x8 rip=0x4d9617`.

Disassembly at and around `$pc` (from the same gdb session, `x/10i $pc-20`):

```
0x4d9603 <hm_hash_text+3>:  push %rsi
0x4d9604 <hm_hash_text+4>:  push %r13
0x4d9606 <hm_hash_text+6>:  push %r12
0x4d9608 <hm_hash_text+8>:  push %rbx
0x4d9609 <hm_hash_text+9>:  call   0x800d80 <lib__common__target__PointerSize.bytes>
0x4d960e <hm_hash_text+14>: mov    %rax,%rbx
0x4d9611 <hm_hash_text+17>: and    $0xfffffffffffffff8,%rax
0x4d9615 <hm_hash_text+21>: je     0x4d968a <hm_hash_text+138>
=> 0x4d9617 <hm_hash_text+23>: mov  0x8(%rax),%r15     ; rax=8 -> reads addr 0x10 -> SEGV
0x4d961b <hm_hash_text+27>: test %r15,%r15
```

### Why this attribution is trustworthy, not a nearest-symbol artifact

- `$pc` (`0x4d9617`) falls 23 bytes into `hm_hash_text`'s own prologue, which
  gdb resolved via the binary's retained `.symtab` — this is a call
  **within** the function's real address range, not a jump into an unmapped
  or unrelated region. `$pc` is neither 0 nor near 0.
- The call at `0x4d9609` targets `0x800d80`, a **real, defined, nonzero**
  function address (`lib__common__target__PointerSize.bytes`) — this is
  exactly what the 2026-08-09 doc's `check-no-call-zero.shs` result
  (0 call-to-zero sites) predicts. It is a **wrong-callee** bind, not a
  call-to-null.
- `rax=0x8` after that call is `PointerSize.bytes`'s known return value (the
  constant pointer size), and `0x8 & ~7 = 8`, so the subsequent
  `mov 0x8(%rax),%r15` reads address `0x10` — matching the `si_addr=0x10`
  reported by the earlier campaign bit-for-bit.
- The full 6-frame backtrace (`hm_hash_text` → `_driver_text_bucket_set_has`
  → `CompilerDriver.load_sources_impl` → `CompilerDriver.compile` →
  `run_native_build_bootstrap` → `main`) is internally consistent with the
  driver's known control flow (source-loading calls into the hashmap
  interpreter helper) and matches the 2026-08-09 doc's backtrace frame names
  exactly, modulo a few return-address bytes (`0x4d9b77`/`0x4d9b69` there vs
  `0x4d9617`/`0x4d9609` here) — expected, since these were two different
  builds of the same source at slightly different points and are not
  claimed to be byte-identical.

**Verdict: this is the documented `text.bytes()` → `PointerSize.bytes`
suffix-scan hijack** (`stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md`),
reproduced independently today from a from-scratch gdb session, not copied
from the prior doc's transcript. It is **not** the nil-receiver SIGILL bug
(`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`) —
that bug's `[mir-stmt-caller]`/`[mir-garbage-expr]`/SIGILL signals require
reaching MIR lowering, and this crash happens during source-loading, before
the frontend or HIR ever runs. It is also not a new fault: same faulting
callee (`PointerSize.bytes`), same wrong-callee mechanism, same
register/address signature (`rax=8`, `si_addr=0x10`).

## Root cause (confirmed still present in current `origin/main` source)

Read `src/compiler_rust/compiler/src/codegen/llvm/functions.rs` at the
suffix-scan block (~line 2675 onward, current tip `e1b85cf56483a1`) and
`codegen/llvm/mod.rs:29` (`qualified_runtime_method_owner_is_builtin`).
Since 2026-08-09 a receiver-type/arity narrowing pass was added at this site
(`if matches.len() > 1 { ... narrow by receiver type ... }`), which reduces
false hijacks in genuinely ambiguous cases — **but it only activates when
`matches.len() > 1`.** For `text.bytes()`, the suffix scan finds exactly
**one** module symbol ending in `.bytes` (`PointerSize.bytes`), so
`matches.len() == 1` and the code path returns that single candidate
immediately, bypassing the new narrowing entirely. This is exactly the gap
the 2026-08-09 doc's fix direction named: *"refuse a candidate whose owner
is a user/unrelated type when the leaf is a known runtime-intrinsic name"*
— still not implemented for the single-candidate branch.

**Caveat on freshness:** the binary exercised here was built from pinned
commit `94b861249c5718dd3a58881f924ccb4b94036661` (2026-08-09), not rebuilt
from the current worktree tip `e1b85cf56483a1d1995b40da73a3bcb0b79e94f5`
(2026-08-10) — this worktree has no prebuilt Stage-2 binary and no
`build/bootstrap/` artifacts (known worktree-isolation gap), and a full
from-scratch Rust-seed + Stage-2 rebuild was out of budget for a
root-cause-only task. The source-code read above is against the current tip
and confirms the vulnerable code path is unchanged there; the binary-level
reproduction is against the pinned commit. These two facts together are the
basis for the verdict, not a claim that today's exact tip was rebuilt and
crashed.

## Fix location (not implemented here, per task scope)

Same as the 2026-08-09 doc identifies:
`src/compiler_rust/compiler/src/codegen/llvm/functions.rs`, suffix-scan
block (~2675-2750). The single-candidate branch (`matches.len() == 1`) needs
the same owner-type check the multi-candidate branch now has: when the sole
suffix match's owner is a builtin/unrelated type (e.g. `PointerSize`) but the
receiver's static type is `text` (or otherwise incompatible), reject the
candidate and fall through to the last-resort intrinsic table
(`mod.rs`'s well-known-method table, which already has the correct
`"bytes" => Some("rt_string_bytes")` entry) instead of silently binding
across owners.
