# Hosted + libsimple_native_all: Rust argv family overrides the C array owner, args silently empty

Status: OPEN. P1.
Parent class: `dynamic_runtime_lane_dual_rt_definitions_2026-09-06.md`
Component: `src/compiler_rust/runtime/src/value/args.rs:248`, `src/runtime/runtime_native.c:7896-7931`

## Reproduction

The run-13 Stage 2 compiler (sha256 `ef163123…ae5a`) builds
`build/repro/r3/main.spl`, a program that only prints
`sys_get_args().len()`:

```
--backend=cranelift --runtime-bundle host-gpu \
  --runtime-path <run-13 phase2-runtime-capsules/ef16…>
```

`./r3gpu x y` prints `direct=0` and no diagnostic.

The link line is the host C objects followed by
`<capsule>/libsimple_native_all.a`, with `--allow-multiple-definition`.

## Mechanism

- `simple_entry.o`'s `main` calls `spl_init_args(argc=3)`.
- `runtime_native.c` declares `rt_get_args`, `sys_get_args`, `rt_cli_get_args`
  and `rt_set_args` as `SPL_WEAK`. The Rust archive defines strong
  `#[no_mangle]` versions, and a strong archive definition beats a weak object
  definition. So `sys_get_args` goes to Rust `rt_get_args`.
- Rust `rt_get_args` calls `rt_array_new`, which resolves to the C version
  (C is strong and appears first). It then calls Rust `rt_array_push_grow`,
  which C does not define.
- `rt_array_push_grow` type-checks the C-allocated array against Rust's
  `HeapObjectType::Array`, fails, and returns 0 (seen in gdb). The array
  stays empty.

## Why not fixed with the sibling row

Making C's argv family strong on ELF would collide with the seed's
exact_stage4 lane. That lane links the C runtime beside the Rust capsule
without muldefs (see the `rt_set_args` comment, `runtime_native.c`). The
designed fix is the 09-06 one: project the Rust archive so that every name the
C objects define is ceded. COFF already does this
(`llvm_runtime_owner_c_archive_v1` / `_c_gnu_archive_v1`). There is no ELF
equivalent.

## Unblock condition

An ELF owner=c projection of `libsimple_native_all.a` in the hosted
cranelift/GNU link path. Pin it with the same
`rt_cli_args_owner_order_selfcheck.c` linked against the projected archive.
