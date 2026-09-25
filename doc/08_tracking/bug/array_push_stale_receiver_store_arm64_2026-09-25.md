# aarch64 native lane: `arr.push(v)` stale-receiver store on growth (65th element)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up)
Severity: latent data-loss; currently masked by the 64-element minimum capacity
in `rt_array_new`, so only arrays that grow past their created capacity on the
aarch64-unknown-none target lose elements.

## Symptom

On the aarch64 cranelift native lane, `arr.push(v)` silently loses the pushed
element whenever the push triggers a capacity growth (i.e. the 65th push into a
default `[]`, or any push past an explicitly created capacity).

## Root cause (byte-exact, two independent confirmations)

The compiler models `arr.push(v)` as an in-place mutating call whose value is
the receiver itself: `lowering_expr_method.rs` (~line 1905) emits
`Call { dest: None, target: "rt_array_push", args: [receiver, val] }` and
yields `receiver_reg`, with the comment "rt_array_push returns bool (success),
NOT the array". That matches the canonical hosted runtime
(`runtime_native.c: rt_array_push(SplArray*, int64_t) -> int8_t`, header
stable, in-place append).

The freestanding aarch64 stub
(`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`) implements
a DIFFERENT ABI: `RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val)`
grows via `realloc`, and this lane's `realloc` ALWAYS allocates a new block and
copies (never extends in place). So on growth the array HEADER MOVES and the
new header pointer is returned in x0 — which the generated code never captures.

Generated shape (from `MountTable.mount` in
build/os/simpleos_arm64_clang_bringup.elf @ 0x40271858, and reproduced
byte-identically by a minimal repro):

```
ldr  x26, [x27]        ; x26 = arr (pre-call)
mov  x0, x26
blr  rt_array_push     ; x0 = NEW header (moved)
str  x26, [x27]        ; stores the STALE pre-call header
```

The same wrong register is stored for statement-position pushes in loops
(`tasks.push(nil)` in `_fs_exec_new_bootstrap_scheduler` @ 0x40368c38 reloads
the receiver from its stack slot every iteration and never stores x0 back), so
`while i < n: arr.push(x)` only ever retains elements that fit the capacity
the array was created with.

## Why most of the kernel works anyway

`rt_array_new` clamps `cap` to a 64-element minimum, so the first 64 pushes of
every default array are in-place appends with a stable header and accumulate
correctly. This is why the module-init set and the fd_table `[u8; 65536]`
fills (post Blocker-4 cap-decode fix) behave: they never push past created
capacity. The failure needs BOTH (a) growth past created capacity AND (b) the
compiler not capturing the return — which is exactly the fused
`self.f = self.f.push(v)` / statement-push shapes.

Note the temp-local split does NOT dodge it: `var t = arr.push(v); arr = t`
is copy-propagated back into the identical stale-store shape (verified with a
minimal repro compiled by bin/simple). No source-level spelling of push avoids
the miscompile; this must be fixed in the compiler or the runtime ABI.

## Fix options (compiler/runtime lane, NOT the clang bring-up lane)

1. Compiler: on growth-capable runtimes the `arr.push(v)` expression value must
   be the call result (`dest: Some(v)`), and statement-position pushes must
   rebind the receiver local from the result. Requires per-target ABI
   knowledge in MIR lowering (today it is target-agnostic).
2. Runtime: make the freestanding rt_array_push honor the canonical
   stable-header ABI (header/data split like `runtime_native.c`), which also
   requires the compiler's inlined accessors (`u32 len@8; u32 cap@12; items@16`
   per 1b3e40d8b9b) to load through a data pointer — a second ABI change.

## Evidence

- build/os/simpleos_arm64_clang_bringup.elf (run-20260925_154638 kernel):
  `MountTable.mount` @ 0x40271858-0x40271878 (stale store),
  `_fs_exec_new_bootstrap_scheduler` @ 0x40368c38-0x40368c70 (loop, no store-back).
- Minimal repro (/tmp/push_repro/repro.spl, compiled with bin/simple
  native-build --target aarch64-unknown-none --backend cranelift): both the
  fused `b.items = b.items.push(v)` and the split
  `var t = b.items.push(v); b.items = t` forms emit `str x22, [x20]` with the
  push result in x0 discarded.
