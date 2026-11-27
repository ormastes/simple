# Native lambda unsafe-block capture traversal

## Observed failure and accepted scope

The native lockless-map boundary specification fails before any of its five
cases execute. The generated outer `describe` callback at `entry.spl:64:48`
reports `cannot materialize lambda for its declared function slot`.
The input source is `3e4dfcdce0d375dbe3c92ee63d891e84f70cc795`; the generated
entry SHA-256 is `39991d7c55e8d4c70f8bac1adb61aeb0d9777fda150dc49c1358294df9dd35a2`.
The actual pure-Simple producer SHA-256 is
`9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`.
Original logs and immutable source remain under
`/tmp/incremental-runner-qualification-20261031/attempt4/`.

The user-authorized scope is a compiler repair that preserves every requested
test and its assertions. Diagnostic reductions do not replace the real suite.

## Cause and implementation boundary

`std.spec` resolves through `std.nogc_async_mut.spec` to the defining
`std.nogc_sync_mut.spec`. Both `describe` and `it` take `block: fn()`.
Each test contains an explicit `unsafe(capabilities: [ffi])` block.
HIR represents this as `UnsafeBlock(HirBlock)`, distinct from `Block(HirBlock)`.
All three closure traversals currently handle `Block` but omit `UnsafeBlock`:

- `lambda_body_captures` treats its unknown form as potentially capturing.
- `lambda_capture_scan_supported` refuses the unknown form.
- `collect_free_var_syms` does not traverse its statements or tail.

The first two decisions make `lower_lambda_value_for_type` return `nil` before
lifting the outer callback. Accept `UnsafeBlock` alongside `Block` in precisely
these three traversals. Reuse the existing lexical binding, statement and tail
rules. Keep unknown expressions refused. Do not rewrite imports or lift test
bodies into named functions to evade closure conversion.

`expr_dispatch.spl` remains the sole lowering owner: it increments and restores
`unsafe_depth` around the actual block. Capture analysis grants no capability,
does not move operations across the unsafe boundary, and does not make unknown
inline assembly or other unsupported inner forms admissible.

## Evidence and acceptance

Retain the failing plain/unsafe differential on the original producer before
editing. After rebuilding the compiler, execute the same unsafe fixture and
check actual values, then cover an outer read, assignment-only capture, lexical
shadowing/nested unsafe, unsafe inside branches/loops, and unsupported inner
forms. Plain counterparts guard against unconditional admission. The unchanged
five-case lockless-map suite must ultimately execute its real assertions.

A source-only patch cannot change the old producer. One shared compile-only
`src/app/cli/bootstrap_main.spl` rebuild is coordinated by the parent bootstrap
lane, with immutable lineage and private caches. Require the resulting compiler
to compile Hello and execute its output before dependent provisional checks.
New compiler and suite evidence remain pending until observed; neither an
authored regression nor the existing file-level runner error is a case PASS.

## Ownership and review

Astra owns diagnosis/design and final patch review. Luna owns the narrow source
edit and diagnostic/regression fixtures. Sol independently accepted the design
and requires the capture/scope negative controls above. The root session owns
source integration, the shared compiler rebuild, required broader checks and
PR landing. This lane does not mutate qualification snapshots or build caches.
