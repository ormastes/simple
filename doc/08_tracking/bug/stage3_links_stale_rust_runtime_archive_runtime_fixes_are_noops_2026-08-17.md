# Stage 3 links a STALE Rust runtime archive — every runtime-side fix is a silent no-op there

Date: 2026-08-17
Status: OPEN — blocker for all runtime-side stage-3 work
Severity: high (invalidates ablation on any `src/compiler_rust/runtime/**` change)

## Verdict

`8510a8368ca` ("receiver-dispatch Dict in rt_clear") **is not present in the binary
that runs stage 3**, and never was. The claimed causal chain
`fix ⇒ enum-payload errors 7,069→0 ⇒ new SIGSEGV at parse 1/619` is therefore
unsupported: no ablation arm can have differed in `rt_clear`, because both arms
linked the same pre-fix archive. This is a fifth refutation, and it refutes the
premise rather than a hypothesis.

## Measurements (static, reproducible, not inference)

Binary that runs stage 3:
`/mnt/data/worktrees/simple-boot-snap/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
(131,328,592 B, mtime 2026-08-17 13:34:51 — i.e. **14 minutes after** the 13:20 commit).

1. **No Dict arm in the linked `rt_clear`.** `objdump -d --disassemble=rt_clear`
   shows exactly three arms: one `get_typed_ptr` (array) → indirect
   `rt_array_clear`; `string_as_str` → `short_string_cache`; else
   `refuse_non_text_receiver`. That is the pre-fix source verbatim. The
   post-fix code would show a **second** `get_typed_ptr` call.
2. **Same result in the admitted archive itself.** In
   `stage2-runtime-authority/libsimple_native_all.a`
   (sha256 `18b81b76b35946f4…`, the hash recorded in `runtime-before-stage3.txt`),
   member `simple_native_all-0d1e749cf08326b1.…cgu.04.rcgu.o`'s `rt_clear` carries
   a single `R_X86_64_PLT32 … get_typed_ptr …` relocation. Pre-fix.
3. **The snapshot SOURCE does have the fix** —
   `src/compiler_rust/runtime/src/value/collections.rs:3230` has the
   `HeapObjectType::Dict` arm. Source and linked archive disagree.
4. **The C runtime is not linked into that binary at all.** `nm --defined-only`
   finds 0 definitions of `rt_core_as_dict`; `rt_clear`/`rt_dict_clear` are the
   Rust ones (mangled `simple_runtime::…` callees). So the C half of
   `8510a8368ca` is shadowed and irrelevant to stage 3, and the "C lane exits 70"
   observation cannot apply either. Both halves of the commit are inert here.
   No runtime `.so` exists (`objdump -p`: only libm/libunwind/libz/libzstd/
   libtinfo/libstdc++/libgcc_s/libc), so there is no late-binding escape.
5. **The errors were never driven to 0.** The live stage-3 log
   `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
   (630,109 B, 13:42) is full of `enum payload dependency … resolved to non-type
   binding …`, e.g. `TokenKind` → `asm_arm_backend` (kind `const`) — a bound name
   with no relation to the requested type, the stale-symbol-id signature. The
   run ends `milestone=exit-2`, with `phase=parse done=619 total=619` (parse
   COMPLETES) and RSS climbing to 16.6 GB during the error flood. Neither
   "log 1,174 B", nor "0 errors", nor "exit 139 at parse 1/619" describes the
   current lane.

## Mechanism

`scripts/bootstrap/bootstrap-from-scratch.sh` fingerprints the Rust inputs by
CONTENT and correctly detects staleness — then declines to act on it:

```
    else
      echo "WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed."
```

The Rust authority archive is only rebuilt under `--full-bootstrap`
(`rust_authority_root="${output_dir}/rust-authority-${seed_inputs_fingerprint}"`
sits inside `if [ "${full_bootstrap}" -eq 1 ]`). Without that flag the run
proceeds on a known-stale archive with a warning, so *any* edit under
`src/compiler_rust/runtime/**` is a no-op for stages 2 and 3 while the source
tree claims the fix.

## What actually moved the enum-payload errors

Snapshot HEAD `513cbb7b4` ("fix(hir): payload-owner test must positively
enumerate type kinds", 10:08, `20.hir/hir_lowering/_Items/module_lowering.spl`)
is a `.spl` change on that exact error path: it replaces the never-firing
`existing_kind == ""` test with `hir_payload_kind_is_type`, and — in the same
commit — adds a re-entrancy breaker to `register_imported_type_methods`
documenting an *already-diagnosed* stage-3 SIGSEGV with `rsp` on the guard page
(`doc/08_tracking/bug/stage3_register_imported_type_methods_infinite_recursion_2026-08-17.md`).
Removing 7,069 spurious `return false` early exits makes that recursion cycle
reachable — the "unmasking" shape, but located in HIR lowering, not the runtime.
That commit, not `rt_clear`, is where both the error delta and the SEGV live.

## Do next

1. **Fail closed on a stale runtime archive** (or rebuild it) instead of warning:
   a stage-3 verdict produced against an archive whose content fingerprint does
   not match the source tree is not evidence about the source tree.
2. Re-run the `8510a8368ca` ablation only under `--full-bootstrap`, and gate it
   on the disassembly check in §1 above (two `get_typed_ptr` calls in `rt_clear`)
   so an arm that silently reused the stale archive is detected, not reported.
3. `8510a8368ca` is not refuted — it is **untested** on stage 3. It remains
   correct on its own terms; keep it.

## Not re-derivable from mtime alone

`build/bootstrap/rust-authority-e1518ace…/…/libsimple_native_all.a` in
`simple-main` is `b59d82fc33dfb81b` (02:15), while the snapshot admitted
`18b81b76b35946f4` copied at 13:29 — different files, both pre-fix. mtime says
"13:29" and is misleading; the disassembly is the only reliable signal.
