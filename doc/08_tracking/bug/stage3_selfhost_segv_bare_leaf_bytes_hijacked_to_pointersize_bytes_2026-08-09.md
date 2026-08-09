# Stage-3 self-host SIGSEGV — bare leaf `bytes` suffix-matched to `PointerSize.bytes`

Date: 2026-08-09
Status: **ROOT-CAUSED, NOT FIXED.** Genuine, new, pre-existing defect. **Not** a
recurrence of the `call 0` artifact — verified, see "Not a call-to-zero" below.
Measured on a pinned clean build of `8ddd09f6d92`. **`origin/main` has since
reverted that commit's untyped last-resort routing** in favour of a typed
HIR/MIR repair, on the (correct) reasoning that *"a leaf name does not prove a
text receiver and can hijack unresolved custom methods."* This bug is the
**concrete measured instance** of exactly that hijack class — and it matters
independently, because it happens in the **suffix scan**, which runs *before*
any last-resort routing and is therefore untouched by either the original fix or
its revert. Re-measure against current `origin/main` before closing.
Area: Rust seed LLVM backend — bare-leaf method call-target resolution
(`codegen/llvm/functions.rs` suffix scan)

## Verdict up front

With `8ddd09f6d92` landed, Stage 2 links clean and **Stage 3 is reachable**. It
crashes with SIGSEGV (exit 139). The crash is **real code at a real address**,
fully symbolized, with a coherent 6-frame backtrace. The Stage-2 binary contains
**0 call-to-zero sites**. This is a different defect from both the link failure
and the address-0 miscompile.

It is a **wrong-callee miscompile**: `s.bytes()` on a `text` receiver is emitted
as a call to `lib__common__target__PointerSize.bytes`, an unrelated zero-content
accessor that returns the constant `8`.

## Authoritative reproduction

Pinned clean worktree at `origin/main` `8ddd09f6d92` (`git archive` + alternates),
`bootstrap-from-scratch.sh --full-bootstrap --jobs=half`:

| stage | result |
|---|---|
| Rust seed / runtime / backfill | clean |
| **Stage 2** | **Linked OK — 809 compiled, 0 cached, 0 failed, 126,032 KB, 0 undefined refs** |
| Stage-2 sanity + capability gate | passed |
| **Stage 3** | **`Segmentation fault (core dumped)` — exit 139**, `stage3-native-build.log` is **0 bytes** (crash precedes any output) |

## Not a call-to-zero (the question this investigation existed to answer)

```
sh scripts/check/check-no-call-zero.shs \
   /home/ormastes/dev/s3crash_out/stage2/x86_64-unknown-linux-gnu/simple
  -> PASS — 1 binary/binaries checked, 0 call-to-zero sites      (exit 0)
```

Independently confirmed with `objdump -d ... | grep -cE 'callq?\s+0 <'` → **0**.
The binary retains its `.symtab`, so gdb symbolizes properly and the
"nearest-symbol misattribution" failure mode of the earlier investigation cannot
occur here. `8ddd09f6d92` closed every call-to-zero instance.

## The backtrace (faithful replay of `stage3-command.transcript`)

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000004d9b77 in compiler.frontend.core.interpreter.hashmap.hm_hash_text ()
#0  hm_hash_text ()
#1  compiler__driver__driver_source_loading___driver_text_bucket_set_has ()
#2  compiler__driver__driver_source_pipeline_loading__CompilerDriver.load_sources_impl ()
#3  compiler__driver__driver_orchestration__CompilerDriver.compile ()
#4  app.cli.bootstrap_main.run_native_build_bootstrap ()
#5  main ()

rax 0x8    si_addr 0x10
```

## The miscompile, instruction by instruction

Source — `src/compiler/10.frontend/core/interpreter/hashmap.spl:24-26`:

```
fn hm_hash_text(s: text) -> i64:
    val bytes = s.bytes()
    val slen = bytes.len()
```

Emitted prologue of `hm_hash_text`:

```
4d9b69:  e8 42 6c 32 00   call   8007b0 <lib__common__target__PointerSize.bytes>
4d9b6e:  48 89 c3         mov    %rax,%rbx
4d9b71:  48 83 e0 f8      and    $0xfffffffffffffff8,%rax
4d9b75:  74 73            je     ...
4d9b77:  4c 8b 78 08      mov    0x8(%rax),%r15     <- SEGV
```

The caller loads the receiver correctly (`mov %rbx,%rdi` at `7e1631`), but the
callee is `PointerSize.bytes`, which ignores `%rdi` and returns the pointer size
**8**. Then `8 & ~7 = 8`, and the `bytes.len()` field load reads `0x8 + 8 = 0x10`
— exactly the `si_addr` observed. The receiver is silently discarded; there is no
nil pointer anywhere in the `.spl` source.

`objdump -d ... | grep -c 'call.*PointerSize.bytes'` → **14** call sites in the
Stage-2 binary, an unknown subset of which are hijacked the same way.

## Root cause

`text.bytes()` reaches LLVM codegen as a **bare leaf** `bytes` with no owner —
the same "no owner at all" shape `8ddd09f6d92` addressed for the six text leaves.
Two mechanisms then interact:

1. `qualified_runtime_method_owner_is_builtin`
   (`codegen/llvm/mod.rs:29-33`) does `dotted.rsplit_once('.')` and **returns
   `false` immediately when the name has no dot**. So for a bare leaf the gate
   fails and the well-known-method table at `functions.rs:2471-2515` — which
   contains the correct entry `"bytes" => Some("rt_string_bytes")` — is
   **skipped entirely**. `rt_string_bytes` and `rt_text_to_bytes` are both
   defined in the binary; the right provider existed and was never consulted.

2. Resolution then falls to the suffix scan at `functions.rs:2675-2746`, which
   searches the module for any function whose name ends with `.bytes`. Exactly
   one matches — `lib__common__target__PointerSize.bytes` — so the
   ambiguity guard at `functions.rs:2733` does **not** fire, and the single
   wrong candidate is silently accepted. No owner-type or arity compatibility
   check is applied.

The bare leaf never reaches `8ddd09f6d92`'s last-resort intrinsic table, because
the suffix scan *succeeds* first — with a wrong, real, defined symbol.

### Why every existing gate is blind to this

- The **link** succeeds: `PointerSize.bytes` is a genuine defined symbol.
- `check-no-call-zero.shs` sees a normal call to a normal address.
- The last-resort diagnostic (`SIMPLE_LLVM_CALL_TARGET_DEBUG=1`) never fires,
  because the fall-through is never reached.

This is strictly worse than the two earlier states: the link failure was loud,
the address-0 bind crashed immediately and universally, but a wrong-callee bind
produces a plausible-looking binary that miscomputes.

## Fix direction (not landed here)

Narrow and inside the same file/pattern as `8ddd09f6d92`:

1. Make the well-known-method table reachable for **bare leaves** — either let
   `qualified_runtime_method_owner_is_builtin` accept a dotless name as
   "builtin owner", or consult the table before the suffix scan when the name
   has no owner.
2. In the `functions.rs:2675` suffix scan, **refuse a candidate whose owner is a
   user type when the leaf is a known runtime-intrinsic name**, so it falls
   through to the last resort instead of binding across owners.

Both need a regression pinning `bytes` on a `text` receiver to `rt_string_bytes`
and *not* to any `*.bytes` user method, in the style of the two `#[cfg(test)]`
regressions `8ddd09f6d92` added to `codegen/llvm/mod.rs`.

Do **not** "fix" this by adding `bytes` to the last-resort table alone — the
suffix scan runs first and would still win.

## Relationship to the nil-receiver SIGILL bug

**Unrelated, and that bug remains UNVERIFIED.**
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md` lives in
50.mir lowering. This crash is in the **driver's source-loading phase** (frame
#2, `load_sources_impl`), long before MIR. The run was instrumented with
`SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1`; the Stage-3 log
is 0 bytes, so **`[mir-stmt-caller]` = 0, `[mir-garbage-expr]` = 0**, no SIGILL,
no exit 132. The SIGILL fault site has **still never executed**. This is
**blocker 15**, sitting in front of it.

The superficial resemblance ("nil receiver") is misleading: there is no nil
receiver here. The receiver is a valid `text` that the callee never reads.

## Status of the related docs (measured at `8ddd09f6d92`; not edited here,
## because `origin/main` has since moved those lanes forward)

- `stage2_native_build_link_undefined_method_symbols_2026-08-09.md` — at
  `8ddd09f6d92` Stage 2 linked clean, 809/809, 0 undefined refs. That doc is now
  `OPEN` again on `origin/main` under the typed-repair plan; this measurement
  does not contradict it and is not merged into it.
- `stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md` — its open question
  ("re-run `check-no-call-zero.shs` against the new Stage-2") is **answered:
  PASS, 0 sites**, down from 169. Safe to close as a duplicate.
- `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md` —
  **still UNVERIFIED.** Its fault site has still never executed; this bug is
  blocker 15 in front of it.

## Artifacts

- Pinned tree: `/home/ormastes/dev/s3crash_8ddd09f` (HEAD `8ddd09f6d92`, clean)
- Output: `/home/ormastes/dev/s3crash_out`
- Crashing binary (has `.symtab`):
  `/home/ormastes/dev/s3crash_out/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
