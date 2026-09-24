# Native: same-named instance methods on sibling types in one module collapse to ONE implementation
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **RESOLVED by PR #867** (2026-09-13,
  `https://github.com/ormastes/simple/pull/867`, "fix(seed): type imported
  static-method calls so sibling instance methods stop collapsing").
- Filed: 2026-09-13
- Supersedes the root-cause analysis in
  `native_u32_u64_span_roundtrip_loses_value_2026-09-13.md` (same symptom, wrong cause)
- Census class: `int-width-bitops` in
  `doc/10_metrics/infra/native_interp_differential_2026-09-13.md` — **the class label
  is wrong**; no integer-width lowering is involved.
- Seed: `build/cargo-f52/release/simple`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 … native-build --mode dynload --backend cranelift`

## What is actually wrong

`src/lib/common/bytes/ints.spl` defines six structs (`U16le`, `U32le`, `U64le`,
`U16be`, `U32be`, `U64be`), each with its own `me store(buf)` / `fn to_span()`.
When those methods are called from **another module**, native codegen binds
*every* `store` / `to_span` call to a **single** implementation — `U32be`'s.

Proof (`nm -gU` on a native binary that calls all six):

```
_common__bytes__ints__U16be_dot_of
_common__bytes__ints__U16le_dot_of
_common__bytes__ints__U32be_dot_of
_common__bytes__ints__U32be_dot_store      <-- the only `store` in the image
_common__bytes__ints__U32be_dot_to_span    <-- the only `to_span` in the image
_common__bytes__ints__U64le_dot_of
```

`static fn of` (a *static* method) is emitted per type correctly. Only
**instance** methods collapse. The other five `store` bodies are never emitted
because no call is ever bound to them.

**The survivor is closure-dependent, not fixed.** In a program importing only
`{U16le, U32le, U64le}` the survivor was `U32le` (`…U32le_dot_store`,
`…U32le_dot_to_span`, `…U32le_dot_value` are the only instance methods in that
image). A 1-unit reproducer can therefore pick the "right" implementation by
luck and look green.

**Why the decode examples pass.** `value()` is also a same-named instance method
on all six types and also collapses — but every body is literally `self.raw`, so
the collapse is behaviourally invisible. `load` is a *static* method and is
emitted per type. Only `store` / `to_span`, whose bodies differ per type, expose
the defect.

## Reproducer (10 lines)

```simple
use lib.common.bytes.span.{ByteSpan, ByteBuffer}
use lib.common.bytes.ints.{U16le, U16be, U32be, U64le}

fn main():
    var b1 = ByteBuffer.new()
    U16le.of(0xBEEF).store(b1)
    print("u16le_len=${b1.len()}")          # interp 2, native 4
    var b2 = ByteBuffer.new()
    U16be.of(0xBEEF).store(b2)
    print("u16be_s0=${b2.freeze().get(0).to_i64()}")   # interp 190 (0xBE), native 0
    val sp = U64le.of(0x0102030405060708).to_span()
    print("u64le=${sp.len()},${sp.get(0).to_i64()}")   # interp 8,8 native 4,5
```

Native `u64le=4,5` is exactly `U32be.store` run over the U64 raw value
(`05 06 07 08`), which pins the surviving implementation.

Interpreter (reference) is correct at every width.

## Why the old "int-width" reading was wrong

The same round trip in a plain `fn main` with only `U32le` in scope **passes
natively** — `U32le.of(0xDEADBEEF).to_span()` → `load(...).value()` returns
`3735928559`. Bit operations, `&`, `>>`, `to_u8()` and byte packing are all
correct at 8/16/32/64 bits. The failure appears only once sibling types with
same-named methods are in the closure, and it is order/candidate dependent —
which is why `U32be round-trips 0xCAFEBABE` is the one round-trip example that
*passes*: it is the surviving implementation.

## Actual root cause (PR #867) — HIR, not the mangler

The suspected site below (`mangle.rs`) was a plausible guess but wrong on two
counts: there is no emission-dedup site (bodies are emitted by reachability
from bound calls — fixing resolution restored emission by itself), and
`mangle_mir` is dead in the reproducing lane (`llvm` feature off,
`--backend cranelift`), so it was never reached.

The real defect is one line in `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`:
the qualified-import arm looked up a callee's return type by the **bare**
method name (`self.named_callable_return_type(method)`), while
`method_return_types` is keyed `Owner.method`. `U16le.of(0xBEEF)` therefore
typed as `TypeId::ANY`, MIR could not qualify the `ANY` receiver, and the
`.store(buf)` call fed to codegen lowered to a **bare** `store` — confirmed
directly via added instrumentation:

```
[HIR-METHOD-RET] .store recv_ty=TypeId(14) recv_hir=Some(Any) -> Void
[MIR-METHOD-DISPATCH] bare 'store' call: receiver ty = Any
```

Every name-keyed resolver downstream (in `codegen/instr/closures_structs.rs`,
the actual load-bearing resolver in the cranelift lane) then bound the bare
`store` to an arbitrary same-named candidate via a `HashMap` first-hit — hence
the closure-dependent survivor.

**Fix:** type the qualified-import callee lookup correctly in HIR (root fix),
plus resolver hardening so ambiguity is refusal, not a coin flip — three
`HashMap`-first-hit-and-break arms in `closures_structs.rs`/`mangle_mir` now
collect distinct candidates and only bind when the scan agrees on exactly one,
and the qualified branch prefers an exact owner match
(`method_owner_matches`, understanding both `Owner.method` and
`Owner_dot_method` spellings). A lone candidate is still accepted (needed for
inherited trait defaults, e.g. `Button.render` resolving to the only emitted
body `Widget.render`) — only a multi-candidate coin flip is removed.

**Evidence (aarch64-apple-darwin):**

| | `_dot_store` | `_dot_to_span` | result |
|---|---|---|---|
| before | 1 | 1 | every `to_span` returned 8 bytes of the u64 raw; 5/6 rows wrong |
| after | 6 | 6 | all twelve values byte-identical to the interpreter |

- Differential harness `bytes/ints_spec.spl` (the 5-6 `int-width-bitops` rows):
  `FAIL — 6 divergent` -> `PASS — 1 spec compared, 0 divergent`.
- Unit tests: sabotage-at-HEAD -> 2 red; with the fix -> 10 passed / 0 failed.
- Full `simple-compiler` lib suite: 3989 passed / 35 failed vs baseline
  3984 / 36 (35 pre-existing arm64/macOS reds) — zero new failures, one
  pre-existing failure fixed.

**Honest gap, not closed by this PR:** the full default differential sample
(multi-hour run) was started on the pinned before-binary and had not returned
when PR #867 was opened, so it was never re-measured against the after-binary.
Only the `bytes/ints_spec.spl` targeted rows and the unit/lib-suite deltas
above are confirmed; a fresh full-sample differential run is still owed.

## Suspected site (original guess, wrong — kept for history)

`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`:

- `:793` — `candidates.iter().find(|c| c.to_lowercase().contains(&type_part.to_lowercase()))`
  is the only receiver-type evidence used; when it misses, the code falls through to
- `:796` the `candidates.len() == 1` arm, and then to
- `:804` `resolve_by_suffix(...)`, which picks a single entry out of the
  same-named candidate vector **without regard to the receiver type**.

Narrowing evidence: the build emits **no** `warning: unresolved call` for
`store` / `to_span`, so the rebind happens at `:793`/`:796`, not at the `:804`
`resolve_by_suffix` fallthrough. It has **not** been confirmed whether MIR hands
the mangler a qualified `U16le.store` or a bare `store`; that is the first thing
the owner should check.

Related (same family, different surface): `co_compiled_duplicate_signature_dispatch_class_2026-08-31.md`
— name-keyed dispatch falling back to "the last definition" for co-compiled free
functions with differing signatures. Here the signatures are *identical* and the
receiver type is the only discriminator, so that fallback has nothing to key on.

The same shape is already documented in this file's own comments for
`Poll.unwrap` (PR #750) and the `str`/`text` UFCS arm; this is a third instance
of the same "bare/under-qualified method name rebinds to an arbitrary candidate"
defect, now affecting ordinary user structs in the stdlib.

Fix direction: instance-method calls must carry the resolved receiver type from
HIR/MIR to the mangler, and a multi-candidate set with no exact owner match must
be an error, never an arbitrary pick.

## Impact

All 6 failing examples of `test/01_unit/lib/common/bytes/ints_spec.spl` under
native build. Any stdlib or user code with same-named instance methods on
sibling types in one module is silently miscompiled natively.

