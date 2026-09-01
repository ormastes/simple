# Kernel-launch grammar has no `stream:` / `shared:` slot — 2026-08-25

Status: OPEN (feature request). Filed while porting
`examples/08_gpu/simple_cuda_example/20.cuda_intermediate/22.Streams_and_Async`
(clone of github.com/ormastes/simple_cuda_example) against the Rust seed.
Per the repo rule ("when a short, safe grammar ... fails ... record a concrete
bug/feature request instead of silently normalizing the workaround") the
module was rewritten to what the toolchain supports, and this record carries
the gap.

## What fails

`22.Streams_and_Async/main.spl` (upstream version) launched on a stream:

```simple
scale_kernel<<<grid: (grid_size, 1, 1), block: (block_size, 1, 1), stream: stream>>>(
    data_dev, scale, n
)
```

Exact diagnostic from `bin/simple run` (seed
`bin/release/x86_64-unknown-linux-gnu/simple`, 2026-08-25):

```
error: compile failed: parse: in ".../22.Streams_and_Async/main.spl": Unexpected token: expected TripleGt, found Comma
```

(The JIT lane reports the same text prefixed with `[INFO] JIT compilation
failed, falling back to interpreter: module load error: parse: ...`.)

## Where

- Parser: `src/compiler_rust/parser/src/expressions/postfix.rs:929`
  (`parse_kernel_launch`). It consumes `<<<`, an optional `grid:` label + expr,
  a comma, an optional `block:` label + expr, then **requires `>>>`**
  (`self.expect(&TokenKind::TripleGt)` at ~:955). There is no loop over
  labelled slots, so a third `, stream: s` (or `, shared: n`) is a hard parse
  error. `grid` is a keyword token (`TokenKind::Grid`); `block` is matched as
  a plain identifier.
- AST: `Expr::KernelLaunch { kernel, grid, block, args }` — no `stream` /
  `shared` fields.
- Interpreter: `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:94`
  evaluates `Expr::KernelLaunch` to `Value::Nil` (documented no-op), so even
  the two-slot form never reaches a device under `bin/simple test` or
  `SIMPLE_EXECUTION_MODE=interpreter`.

## The gap is three layers deep, not one

A grammar fix alone could not work; every layer below it also lacks a stream:

| Layer | State |
|-------|-------|
| Grammar (`postfix.rs:929`) | `grid:` and `block:` only |
| Simple SFFI | `src/lib/nogc_sync_mut/cuda/sffi.spl:93` `rt_cuda_launch_kernel(module, func_name, gx,gy,gz, bx,by,bz, args_ptr)` — no stream, no shared-mem; the `io/cuda_sffi.spl:26` mirror declares a `shared_mem` slot and an `args:[i64]` array but that arity does not match the runtime (Gap B in the 2026-08-25 brief) |
| Runtime | `src/compiler_rust/runtime/src/cuda_runtime.rs:1240-1258` `CudaFunction::launch` passes `ptr::null_mut(), // default stream` to `cuLaunchKernel`; there are **no** `rt_cuda_stream_create/destroy/synchronize` symbols in the runtime (grep of `cuda_runtime.rs` and of the interpreter dispatch table `interpreter_extern/mod.rs` finds only `rt_cuda_event_*`), so `std.io.cuda_sffi.cuda_stream_create` is an unbacked extern |

## Proposed grammar

```
kernel_launch := expr '<<<' launch_slot (',' launch_slot)* '>>>' '(' args ')'
launch_slot   := ('grid' ':' expr)
               | ('block' ':' expr)
               | ('stream' ':' expr)      # default: 0 (legacy/default stream)
               | ('shared' ':' expr)      # dynamic shared-memory bytes, default 0
               | expr                     # positional, in the order grid, block, shared, stream
```

`grid` and `block` remain mandatory; `stream` and `shared` are optional and
order-independent when labelled. `Expr::KernelLaunch` gains
`stream: Option<Box<Expr>>` and `shared: Option<Box<Expr>>`. Positional order
mirrors CUDA's `<<<grid, block, sharedMem, stream>>>` so C++ readers are not
surprised.

## Unblock conditions

1. `postfix.rs` accepts the four labelled slots (+ AST fields, HIR lowering).
2. Runtime: `rt_cuda_stream_create() -> i64`, `rt_cuda_stream_destroy(i64)`,
   `rt_cuda_stream_synchronize(i64)`, and a launch entry taking
   `(shared_mem: u32, stream: i64)` — `cuLaunchKernel` already has both
   parameters at `cuda_runtime.rs:366-380`, only the wrapper hard-codes them.
3. Interpreter dispatch entries for the new externs, and the single
   `rt_cuda_launch_kernel` declaration reconciled between
   `cuda/sffi.spl:93` and `io/cuda_sffi.spl:26`.
4. Regression spec: `22.Streams_and_Async/spec.spl` gains a real two-stream
   overlap example once (1)-(3) land; until then the module runs on the
   default stream and uses `rt_cuda_event_*` for timing.

## Related

- `examples/08_gpu/simple_cuda_example/20.cuda_intermediate/22.Streams_and_Async/README.md`
- `.claude/rules/vcs.md` (unbacked-extern ratchet: adding stream externs to
  `src/lib` without runtime backing would trip
  `scripts/check/check-unbacked-extern-ratchet.shs`).

## Interim form (2026-08-25, plan E4 deferred)
Until the grammar gains `stream:`/`shared:` slots, express a stream launch through the API:
`cuda_launch_on(kfn, cfg, stream, shared_bytes, args)` (std.io cuda_sffi, plan row E2) — same
contract the slot would lower to (`rt_cuda_launch_kernel_ex`). The slot itself is deferred because
the self-hosted AST variant `KernelLaunch(Expr, Expr, Expr, [CallArg])` (`10.frontend/parser_types_expr.spl:406`)
is positional and every construction/match site would ripple.
