# Plan: staged removal of the native-codegen construct blocklist, starting with `match`

**Date:** 2026-08-01
**Status:** Stage 1 implemented and verified; Stages 2-5 planned, not started.
**Owner:** compiler / native backend lane

## 1. Problem

`compile --native` refuses any function containing a `match`:

```
error: semantic: cannot compile to standalone native binary: 1 function(s) contain
constructs that require the interpreter:
  - pick: [PatternMatch]
```

This fires on a minimal two-variant, payload-free enum. It is a global cap, not a
per-subsystem defect.

**Consequence for the evidence record:** any historical claim that a defect
"reproduced on native" for enum-matching code is describing something that could
not have been compiled. Such claims must be re-verified, not trusted.

## 2. Where the refusal lives

| Thing | Location |
|---|---|
| Error emission | `src/compiler_rust/compiler/src/pipeline/execution.rs:1064-1072` |
| Bracketed reason list | `execution.rs:1039` (`format!("{:?}", status.reasons())`) |
| SMF sibling message | `execution.rs:267-292` |
| Analyzer | `src/compiler_rust/compiler/src/compilability.rs` |
| Reason enum | `compilability.rs:15-58` (`FallbackReason`) |
| Analysis entry | `analyze_module` (`compilability.rs:138`) via `execution.rs:961` |
| Pure-Simple mirror | `src/compiler/80.driver/compilability.spl:14-36` |

**The check runs on the AST**, before HIR and MIR — it never sees the lowering
that actually exists. That is the root of the over-approximation.

Escape hatch `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1` / `SIMPLE_BOOTSTRAP=1`
(`execution.rs:1032`) does **not** solve this: it lets the binary link, but every
such call returns nil. It converts a build error into a silent wrong answer.

### 2.1 The full blocklist — all 21 `FallbackReason` variants

Every one of these is an invisible cap on native coverage, not just `PatternMatch`.

| Variant | Emitted at `compilability.rs` | Why it is flagged |
|---|---|---|
| `PatternMatch` | 276 (`Node::Match`), 506 (`Expr::Match`) | **Stale** — see §4 |
| `Closure` | 290 | nested `Node::Function`; no capture codegen |
| `WithStatement` | 281 | scope/resource protocol is interpreter-driven |
| `ContextBlock` | 286 | same |
| `Decorators` | 204 | decorator dispatch is interpreter-side |
| `CollectionOps` | 322 (`in`/`NotIn`), 422 (`Slice`), 642/658 (comprehensions), 668/673 (spread) | |
| `CollectionLiteral` | 445 (`VecLiteral`), 762 (`ArrayRepeat`) | |
| `AsyncAwait` | 358, 535 | |
| `ActorOps` | 363, 529 | |
| `Generator` | 366, 543 | needs interpreter coroutine state |
| `TryOperator` | 549, 555, 562, 769, 777, 781, 790, 799, 803, 810 | `?`, `!`, `.?`, `unwrap_or*`, `cast_or*`, `??` |
| `UserMacros` | 567 | unexpanded at codegen |
| `StringOps` | 601 — **only when `mode != AotNative`** | native lowers via `rt_value_to_string` |
| `MethodCall` | 682 (`FunctionalUpdate`), 823 (`OptionalMethodCall`) | |
| `FieldAccess` | 816 (`OptionalChain`) | |
| `NotYetImplemented(String)` | 311, 331, 523, 607, 623, 627, 687, 691, 698, 706, 732, 739, 746, 828, 833 | symbol, `ref`, `new`, i18n, contract `old()`, quantifiers, grid/tensor literals, atoms, unknown expr |
| `DynamicTypes` | never | dead variant |
| `GcInNogcContext` | never | dead variant |
| `BlockingInAsync` | never | dead variant |
| `ObjectConstruction` | never | dead variant |
| `UnknownExtern(String)` | never (Rust) | only the `.spl` mirror pushes it (`compilability.spl:144`) |

`StructInit` carries an explicit comment that it "is part of the current native
surface" — evidence the list is maintained by *deleting* entries as the backend
catches up. `PatternMatch` was simply never revisited.

## 3. Measured gap

Owned code only (`src/**`, excluding `src/compiler_rust/vendor/`,
`src/runtime/vendor/`). All counts via `/usr/bin/grep` and `awk` (the shell
default here is ugrep, which would have skewed the numbers).

| Metric | Count |
|---|---|
| `.spl` files scanned | 13,901 |
| Function definitions | 115,405 |
| Functions containing any `match` | **10,738** (9.3%) |
| Functions containing an enum-variant `case` arm | **4,228** |
| Files containing any `match` | 3,128 |
| Files in `src/compiler` containing any `match` | 621 of 1,559 (40%) |

Breakdown of the 4,228 enum-matching functions by what blocks them:

| Class | Count |
|---|---|
| **Stage-1 eligible** (payload-free arms + wildcard, no guard) | **591** |
| has a payload-binding arm | 3,608 |
| has a bare-identifier arm | 547 |
| other pattern form (tuple/struct/or/range/literal) | 1,008 |
| has a guard | 27 |

### 3.1 The number that actually matters

The gate is evaluated **per function**, but the refusal is **per compilation
unit** — one non-native function anywhere in the linked closure kills the whole
binary. With 10,738 match-containing functions spread over 3,128 files, and 40%
of `src/compiler` affected, no realistic program closure was native-compilable.

**Therefore: before Stage 1, `--native` was not a usable verification lane for
anything beyond toy programs.** Treat pre-2026-08-01 "verified on native"
statements about enum-matching code as unsubstantiated.

## 4. What lowering already exists

Enum `match` is **already fully desugared** into ordinary ops on both pipelines.
There is no opaque pattern node in either IR.

### Pure-Simple pipeline

- `MirTerminator` — `src/compiler/50.mir/mir_instruction_support.spl:276`:
  `Goto` :278, `Ret` :279, `If` :282, `Switch(value, targets, default)` :283,
  `Unreachable` :286, `Abort` :287, `CallTerminator` :290.
- `MirInstKind` — `src/compiler/50.mir/mir_instruction_kinds.spl:9`. There is
  **no** `PatternMatch`, `Discriminant`, or `GetTag` instruction.
- `lower_enum_match` —
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1356`
  (reached from `lower_match_case`, `.../expr_dispatch.spl:3108`, dispatch
  :3196). Shape: `Call rt_enum_discriminant` (:1362-1366), then per arm
  `emit_const_int(disc)` + `emit_binop(MirBinOp.Eq, ...)` +
  `terminate_if(...)` -> `MirTerminator.If` (:1564-1568). Payload binding is a
  further `Call` to `rt_enum_payload` / `rt_unwrap_or_self`.
- `MirTerminator.Switch` is emitted **only** by `emit_switch_dispatch`
  (:490-520) for dense integer matches; enum matches take the If-chain.

### Rust seed pipeline (what `compile --native` runs today)

- HIR `lower_match` — `compiler/src/hir/lower/expr/control.rs:351`; variant test
  becomes a call to `rt_enum_check_discriminant` (:613-630).
- MIR `Terminator::Switch` — emitted at
  `compiler/src/mir/lower/lowering_expr_control.rs:257` via `lower_int_switch`,
  recovered from an already-desugared `LetIn { ... If chain }` by
  `try_collect_int_match`.
- Consumed by `codegen/instr/body.rs:1192` and `codegen/llvm/instructions.rs:770`.

### Where the two part company

They do **not** part company at match lowering. Native/JIT/LLVM/Cranelift all
consume the same MIR (`src/compiler/70.backend/backend/native/mod.spl:53/66/79/92`
-> `isel_module*`). The interpreter is the outlier: it is a **HIR** tree-walker
(`src/compiler/70.backend/backend/interpreter.spl`, `rt_enum_discriminant` :16,
dispatch :255/:651) and never sees MIR at all.

Native isel already covers every op an enum match needs:

| Need | Existing support |
|---|---|
| discriminant read | `MirInstKind.Call` -> `isel_call` (`isel_x86_64.spl:328`), emits `X86_OP_CALL op_sym("rt_enum_discriminant")` :358 |
| tag compare | `MirBinOp.Eq` |
| branch | `MirTerminator.If` -> `X86_OP_TEST` + `X86_OP_JNZ` + `X86_OP_JMP` :597-603 |
| dense dispatch | `MirTerminator.Switch` :604-611 — currently a linear `CMP_IMM`/`JE` chain, **not** a real jump table |

isel coverage: `isel_x86_64.spl` (:163-193, terminators :578-613),
`isel_aarch64.spl` (:251-277 / :634-644, no `GetElementPtr`/`Aggregate`),
`isel_riscv64.spl` (:306-336 / :705-715), `isel_riscv32.spl` (:301-329 /
:659-669, no `Intrinsic`). `CallTerminator` and `Abort` fall into the `case _ ->
NOP` default in every isel — a separate latent gap worth its own item.

Runtime helper: `src/runtime/runtime.c:1248`,
`src/runtime/runtime_native.c:5105`, decl `src/runtime/runtime.h:479`, Simple
side `src/runtime/simple_core/core_enum.spl:49`.

**Conclusion: `PatternMatch` on the blocklist was a stale AST-level
over-approximation, not a missing backend.** Stage 1 is a gate correction, not
new codegen.

## 5. Stage 1 — payload-free enum matches (IMPLEMENTED)

`is_native_payload_free_enum_match` in `compilability.rs` accepts a match, in
`AotNative` mode only, when every arm is a payload-free `Pattern::Enum` or
`Pattern::Wildcard` and no arm has a guard.

It also fixes an adjacent blind spot: arm **bodies were previously never walked
at all** — the blanket `PatternMatch` reason made it moot. They are now analyzed,
so a match accepted natively cannot smuggle an unsupported construct past the gate.

### Verified (rebuilt seed, `compile --native`, binary executed)

| Probe | Result |
|---|---|
| 2-variant payload-free | compiles, prints `1` |
| 3-variant payload-free | compiles, prints `10` / `20` / `30` — **discriminates correctly**, not always-first-arm |
| variant + `case _` wildcard | compiles, prints `9` / `1` |
| payload arm `case Shape.Line(n)` | still refused |
| bare identifier `case other` | still refused |
| guard `case Color.Red if n > 0` | still refused |
| no match at all (control) | still compiles, no regression |

The 3-variant probe is the load-bearing one: it proves real tag dispatch, which
distinguishes a working lowering from an always-match.

**Slice removed: 591 functions.** Small in absolute terms, but it is the first
non-zero native coverage for enum code, and it establishes the verification
pattern for later stages.

## 6. Interaction with two defects landed 2026-08-01

Both are live on the compiled lanes and **must not be inherited** by any native
lowering. This is why Stage 1 is deliberately narrow.

1. **Nested payload sub-patterns always match and never bind.**
   `Const(MirConstValue.Str(x), _)` matches unconditionally and leaves `x`
   unbound on JIT and native; the interpreter is correct, so no interpreter-run
   spec catches it. Any stage that admits payloads must first fix this, and must
   gate on a **negative** probe (a case that must NOT match) — a positive-only
   probe passes vacuously against an always-match bug.

2. **A bare identifier in `case` position is an irrefutable binding.**
   `doc/.../case_bare_ident_is_irrefutable_binding_2026-08-01.md`. `case other:`
   is not a variant test; it binds and matches everything. Stage 1 therefore
   rejects `Pattern::Identifier` / `MutIdentifier` / `MoveIdentifier` outright
   rather than treating them as variant names. This affects 547 functions, which
   stay blocked on purpose.

Neither defect can reach Stage-1 code: payloads and bare identifiers are both
excluded by construction.

## 7. Staged plan

Each stage: extend the gate predicate, then prove with a probe that includes at
least one **negative** case (a variant that must not be selected) and one
multi-variant case. Land each stage separately.

- **Stage 2 — literal and dense-integer arms.** `Pattern::Literal` over integer
  and bool subjects. Backend support already exists
  (`lower_int_switch`/`try_collect_int_match`). Small.
- **Stage 3 — guards.** Accept `arm.guard` once each guard expression itself
  passes `analyze_expr`. Only 27 functions; do it for uniformity, not volume.
- **Stage 4 — payload binding (single level).** Blocked on defect (1). Requires
  fixing bind emission on the compiled lanes first, then admitting
  `Pattern::Enum { payload: Some(..) }` where every sub-pattern is a wildcard or
  a fresh binder. This is the big one: **3,608 functions**.
- **Stage 5 — nested sub-patterns, `Or`, `Tuple`, `Struct`, `Range`.** 1,008
  functions. Only after Stage 4 is proven with negative probes.

Independent, orthogonal follow-ups surfaced by this work:

- **Real jump tables.** `MirTerminator.Switch` currently lowers to a linear
  `CMP_IMM`/`JE` chain in `isel_x86_64.spl:604-611`. Enum matches do not even
  reach `Switch` (they take the If-chain) — routing dense payload-free enum
  matches through `Switch`, and giving `Switch` a real `br_table`, are two
  separate improvements. Neither is required for correctness.
- **`CallTerminator` / `Abort` are silent NOPs in every isel.** Latent
  wrong-code risk, unrelated to `match`; file separately.
- **Delete the four dead `FallbackReason` variants** (`DynamicTypes`,
  `GcInNogcContext`, `BlockingInAsync`, `ObjectConstruction`) — they can never be
  reported and make the blocklist look larger than it is.
- **Port the gate to the pure-Simple mirror.** `compilability.spl:120-146` is a
  string-keyed stub, not an AST walker. It is not what produces today's error,
  but it will need the same predicate once the self-hosted binary owns
  `--native`.

## 8. What this plan deliberately does not do

No attempt at a full pattern-match codegen path. The measured gap (§3) and the
proven-stale gate (§4) are the deliverable; a half-finished lowering that
silently mis-dispatches would be worse than the current honest refusal — and,
given defect (1), it is exactly the failure mode already in evidence.
