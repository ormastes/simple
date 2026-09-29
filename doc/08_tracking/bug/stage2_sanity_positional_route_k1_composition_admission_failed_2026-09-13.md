# Site 16: the Stage-2 candidate refuses a POSITIONAL entry — `PLUG-E-K1-POLICY: bootstrap backend composition admission failed`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: ROOT-CAUSED, fix landing (2026-09-13, macOS F72 lane) -- see "Root cause" at the end; the MIR-lowering suspect below is retracted
- Area: `src/app/cli/bootstrap_main.spl` in-process native-build route / K1 static
  backend composition admission / Stage-2 sanity gate
- Found by: BOOT-15, run B (`build/bootstrap-boot15b`, head `a59b81f9e1c`,
  `--full-bootstrap --backend=llvm --mode=dynload --jobs=10 --stop-after-stage2`),
  16:17:30 -> 16:31:10, rc=1
- Blocks: Stage-2 **admission**. The candidate builds and links fine (site 15 is
  closed: `Build complete: 889 compiled, 0 cached, 0 failed`), `--version` answers
  `simple-bootstrap 1.0.1-beta.1`, and three of the four frontend probes pass. The
  gate stops at `stage2-sanity.env` `status=fail`, so Stage 3 and Stage 4 are still
  unreachable.
- Candidate: `build/bootstrap-boot15b/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
  152416216 B, sha256 `c371050573bcbf03f9b238b9f5cb0448c8118ba0d9b111246acc3a59b0c10016`
  (pinned exec copy: `scratchpad/boot15/pin/cand.boot15b.stage2`)

## Symptom

`stage2-sanity.env`: `status=fail`, `frontend_smoke_status=1`,
`frontend_smoke_bootstrap0_raw_status=1`, and — because the gate short-circuits —
`frontend_smoke_bootstrap1_ran=false`.
`...frontend-bootstrap-0.status.env` names the probe: `probe=hello-world-positional-build`,
`raw_status=1`, while its three siblings are green (`p2_add_raw_status=0`,
`stage2_mir_retention_raw_status=0`, `stage2_module_path_naming_raw_status=0`).

The probe's whole log is one line:

```
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
```

## Reproduced outside the gate in seconds — and the gate's framing is WRONG

`scratchpad/boot15/repro16.sh` replicates `candidate_frontend_admission.shs:549-568`
argv-for-argv and env-for-env, and varies exactly two things. Measured on the pinned
candidate:

| row | `SIMPLE_BOOTSTRAP` | entry form | rc | output | first line |
|---|---|---|---|---|---|
| pos0 | 0 | **positional** | 1 | ABSENT | `PLUG-E-K1-POLICY: bootstrap backend composition admission failed` |
| flag0 | 0 | `--entry` | **0** | present | (builds normally) |
| pos1 | **1** | **positional** | 1 | ABSENT | `PLUG-E-K1-POLICY: …` |
| flag1 | **1** | `--entry` | **0** | present | (builds normally) |

**The bootstrap mode is irrelevant; the entry FORM is the whole variable.** The
sanity gate reports this as a `bootstrap-0` leg failure only because leg 0 runs
first and the gate stops there — leg 1 would have failed identically. Anyone
reading `frontend_smoke_bootstrap0_raw_status=1` as "the SIMPLE_BOOTSTRAP=0 leg is
broken" (a conclusion this repo has reached before) is being misled by the
ordering.

## Why the two forms diverge (source, not inference)

`run_native_build_bootstrap` (`src/app/cli/bootstrap_main.spl:343`) splits at :381:

- `--entry <file>` and not Stage3/Stage4 -> `return run_rt_native_build(args)`
  (:388). It **never reaches** the in-process route.
- a POSITIONAL entry falls through to `val entry_path =
  native_build_single_spl_positional(args)` (:399) and enters the direct
  `CompilerDriver` route, which at **:431** requires
  `install_selected_k1_backend_table_v1()` and returns 1 with this exact message
  when it is false. Its own comment says why: *"This direct driver route bypasses
  the composition wrapper that normally installs K1."*

`install_selected_k1_backend_table_v1` has **two** definitions, shadowed by
identical module path `compiler.driver.bootstrap_k1_selected`:

| file | body |
|---|---|
| `src/compiler/80.driver/bootstrap_k1_selected.spl:7` | fail-closed stub, `-> bool: false` unconditionally |
| `src/compositions/kernel_llvm_cranelift/compiler/driver/bootstrap_k1_selected.spl:32` | the real installer |

`src/compositions/kernel_llvm_cranelift` **is** on Stage 2's argv
(`stage2-command.transcript`, `argv:67`), so the composition root was supplied.
Only one caller of `install_k1_static_backend_table_v1` exists in the whole tree
(the composition itself), so the "already installed under a different policy"
branch at `static_backend_registry.spl:76-77` cannot be what returns false here.

**Discriminated by measurement (runs C and D) — see "Cause pinned" below.** The two
candidates were: Two causes remain and both
produce `false` with no distinguishing output:
1. the STUB bound into the capsule instead of the composition (module shadowing
   resolved the wrong way), or
2. the real installer ran and `validate_k1_static_backend_table_v1`
   (`static_backend_registry.spl:58-70` — a sortedness check plus six
   `BackendKind`/`BackendLinkClass` equality tests over a 3-element array)
   evaluated false in the compiled capsule while being correct on the seed.
Telling them apart needs one extra diagnostic print at
`bootstrap_main.spl:431` naming `selected_k1_backend_policy_v1()` — `"unselected"`
is the stub, `"llvm-cranelift"` is the composition — and a Stage-2 rebuild.

## It is a REGRESSION, by a same-command A/B

The identical repro was run against BOOT-13's ADMITTED candidate
(`cand.boot13b.stage2`, 152289464 B, sha256 `d19daa8c090c2a30ec6f…`), same cwd, same
env, same argv:

```
boot13 candidate, positional:  error: in-process native-build: persistent package index
                               admission failed: scv-authority-missing            <- site 14, LATER
boot15 candidate, positional:  PLUG-E-K1-POLICY: bootstrap backend composition
                               admission failed                                   <- site 16, EARLIER
```

BOOT-13's binary gets **past** K1 admission and into phase-1 source loading; this
tree's binary does not. Since only the binary differs between those two rows, the
K1 admission step regressed in the compiled capsule somewhere between
`8b2516a6477` (BOOT-13's admitted tree) and `a59b81f9e1c`.

Suspect, stated as a suspect: `34b96e29837` (2026-09-13 13:51) is the only commit in
that span that rewrites MIR lowering — `+33` in
`src/compiler/50.mir/_MirLowering/function_lowering.spl`, `+14` in
`mir_instruction_graph.spl`, plus three new `MirFunction` fields threaded through
`apply_function_attr_to_mir` — and `validate_k1_static_backend_table_v1` is exactly
the shape (small fixed array, indexed reads, enum equality) that such a change can
perturb. A one-variable revert was ATTEMPTED here and abandoned: `git revert -n
34b96e29837` conflicts in four files because later commits build on it, so reverting
it would have changed more than one variable. Not asserted as the cause.

## Note for whoever fixes it

`bootstrap/*/simple` stage binaries are the bootstrap CLI, which exposes only
`compile` and `native-build`. The positional form is the one a human types and the
one `stage2_admitted_while_hello_world_native_build_segv_2026-08-25.md` added this
probe for — so "just always pass `--entry`" is not a fix, it is how a compiler that
cannot compile hello world was admitted once before.

## Cause pinned (runs C and D, two one-line diagnostics, two rebuilds)

The message discarded the only fact that separates the candidates, so it was made to
carry it. Both changes are on the error path and change no behaviour.

**Run C** (`build/bootstrap-boot15c`, head `35c52aafd66`, 16:39:34 -> 16:46:57, 7m23s) —
`bootstrap_main.spl` now prints `selected_k1_backend_policy_v1()`:

```
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
  (selected policy 'llvm-cranelift'; 'unselected' means the fail-closed stub bound …)
```

`'llvm-cranelift'`, not `'unselected'` — **the real composition bound into the capsule.
The fail-closed stub is NOT the cause**, and the module shadowing works.

**Run D** (`build/bootstrap-boot15d`, head `89c34061381`, 16:47:55 -> 16:56:15, 8m20s) —
the line additionally reports the two branches that can answer false inside
`install_k1_static_backend_table_v1` (`static_backend_registry.spl:72-81`):

```
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
  (selected policy 'llvm-cranelift', table_valid=false, installed policy '')
```

`installed policy ''` rules out the "already installed under a different policy" branch —
nothing had been installed. So:

> **`validate_k1_static_backend_table_v1("llvm-cranelift", selected_k1_backend_table_v1())`
> returns FALSE inside the compiled Stage-2 capsule**, on a table the same code accepts on
> the seed interpreter.

That is a 13-line pure function (`static_backend_registry.spl:58-70`) and the whole
remaining search space:

- `_table_is_sorted_v1(table)` — the sortedness scan over the 3-entry array;
- `table.len() == 3`;
- six `BackendKind` / `BackendLinkClass` equality tests against array elements
  `table[0..2]`.

One of those evaluates wrongly in the capsule. Narrowing to WHICH needs one more
diagnostic and one more 8-minute rebuild; it was stopped here rather than adding a
single-use reason-reporting helper to a hot validator.

This also sharpens the suspect: a defect in small-fixed-array indexing or enum equality
under MIR lowering is consistent with `34b96e29837` being the only commit in the
BOOT-13 -> here span that rewrites `function_lowering.spl` and `mir_instruction_graph.spl`
— still a suspect, still not proven.

## Root cause (2026-09-13, macOS lane F72 / chain site 18) -- the suspect above is WRONG

`validate_k1_static_backend_table_v1` is not miscompiled by MIR lowering; **every
enum `match` compiled by the Rust seed's `native-build` takes its LAST arm**, so
`BackendKind.to_text()` (a `match self`) returns the wrong text and
`_table_is_sorted_v1`'s `name != entry.kind.to_text()` fails. Reproduced in
seconds outside the lane with a 40-line fixture built by the seed
(`SIMPLE_NATIVE_BUILD_RUST=1`, both `--backend llvm` and `cranelift`):

```
interp:  q_mixed=10,20,30 u_mixed=10,20,30 q_unit=1,2 u_unit=1,2
native:  q_mixed=30,30,30 u_mixed=30,30,30 q_unit=2,2 u_unit=2,2
```

and the discriminating probe (`rt_enum_new` with a chosen enum id, then `match`):
`id=0 -> 10` (wildcard accepted), `id=hash("Mixed") -> 10`, but
`id=<the id the constructor actually stamped> -> 30`. The constructor and the
check disagree on the enum's runtime identity:

- `df7ac9f6cc2` (2026-09-13 13:33) made typed enum matches call
  `rt_enum_check_variant(subject, enum_id, discriminant)`. The Rust seed's HIR
  lowering (`compiler/src/hir/lower/expr/control.rs`, `enum_runtime_id_for_type`
  / `enum_runtime_id_for_pattern`, plus the sibling sites in `expr/mod.rs` and
  `stmt_lowering.rs`) folds `enum_id` into an INTEGER literal from the BARE
  `HirType::Enum { name }` -- `hash("Mixed")`.
- The constructor's `MirInst::EnumUnit { enum_name }` is later rewritten by
  `pipeline/native_project/mangle.rs::qualify_enum_runtime_names` to the
  qualified runtime name -- `hash("pkg.owner.Mixed")` -- but an already-folded
  integer cannot be rewritten, so the two never agree for any enum declared in a
  real module. The seed's own unit test used a bare, module-less enum name, which
  is the one case that agrees.

That is why the Linux BOOT-13 candidate (built before 13:33) got past K1 and
every later candidate did not, on both platforms. `34b96e29837` is not involved.
The same defect also makes the candidate's own `compile --format=smf` die with
`E-AST-SEMANTIC-UNHANDLED: TypeKind at ast_semantic_encode_type` (a `match` over
`TypeKind` falling to its default arm) -- corroboration, not a second bug.

**Fix:** `qualify_enum_runtime_names` now also routes the folded enum-id
`ConstInt` feeding each `rt_enum_check_variant` call through the SAME `qualify`
the constructor uses (ids 0/1 -- Result/Option -- untouched), so ctor and check
agree by construction. Pinned by two Rust tests in
`pipeline/native_project/tests.rs` (`enum_match_check_id_is_qualified_like_its_constructor`,
`..._stays_bare_without_a_module_name`). The K1 gate, the validator and
`to_text()` are unchanged. This has to live in the seed: the seed is the
producer of Stage 2, and no pure-Simple change can correct a seed miscompile of
the Stage 2 binary.

---

---

## ROOT CAUSE FOUND AND FIXED — 2026-09-13 (BOOT-16)

- Status: FIXED in the Rust seed (`7bcf337209f`), pinned by
  `df1ec89c4cf`. Stage-2 effect recorded separately below.

BOOT-15 narrowed this to "a natively compiled `match` on an enum runs no arm:
`rt_enum_new` is baked with one id, `rt_enum_check_variant` with another
(= `rid("Kind")`, the BARE name), discriminants agree", and established that the
pure-Simple sites in `src/compiler/50.mir/_MirLowering/module_lowering.spl` never
execute for Stage-2 output. The two derivations are in the Rust seed, and they are:

| side | site | name it hashes | id for `enum Kind` in module `aa.zz` |
|---|---|---|---|
| construction | `pipeline/native_project/mangle.rs:43` `qualify_enum_runtime_names` rewrites `MirInst::EnumUnit`/`EnumWith.enum_name` to the declaring-module runtime name (module name from `compiler.rs:764` `enum_runtime_module_name_from_path`), which codegen then hashes at `codegen/llvm/functions.rs:1695` / `codegen/instr/calls.rs:2404` | `aa.zz.Kind` (module-qualified, hence path-dependent) | 1815201125 |
| match | `hir/lower/expr/control.rs:1538` `enum_runtime_id_for_type` and `:1545` `enum_runtime_id_for_pattern` bake the id as an HIR `Integer` literal into the `rt_enum_check_variant` builtin call (also `mir/lower/lowering_expr_call.rs:447` for `is_ok`/`is_err`) | `Kind` (bare declared name) | 2107071139 = `0x7d975aa3` |

`2107071139` is exactly the `w1` BOOT-15 disassembled out of the real Stage-2
binary, so the unit-level reproduction and the machine code agree.

The match side was never reachable by `qualify_enum_runtime_names`: by the time
MIR exists the name is already an integer, so the pass saw nothing to qualify.
`rt_enum_check_variant` answers 0 on an id mismatch, so **no match arm ran in any
natively compiled Simple program** — which is why `BackendKind.to_text()` returned
garbage in the capsule, why `_table_is_sorted_v1` was false, and why
`validate_k1_static_backend_table_v1` refused the table. The 13-line pure function
this record narrowed to was correct all along; every `match` inside it was dead.

**Fix** (`7bcf337209f`): `qualify_enum_runtime_names` now also remaps the baked
constant, through the same `qualify` closure the constructors take, so both sides
derive from the one canonical runtime name `imports.rs:519` registers. A fresh
`ConstInt` is inserted before the call rather than the existing one mutated (a
constant vreg can feed other operands); ids 0/1 are never rewritten (reserved
Result/Option lane, and 0 also marks the erased discriminant-only lane); a
bare-name hash collision whose qualified answers disagree drops the entry instead
of guessing.

**Evidence** — private seed `d6f1a424edbc` (before) vs `60adb234b470` (after),
`native-build --backend cranelift`, BOOT-15's `shapes4.spl`, 3 s per iteration:

| shape | interpreted (control) | native before | native after |
|---|---|---|---|
| `match k` -> i64, 3 arms | 11 / 22 / 33 | 0 / 0 / 0 | **11 / 22 / 33** |
| `match k` -> text | cranelift / interpreter / llvm | '0' / '0' / '0' | **cranelift / interpreter / llvm** |
| `match` with `case _` | 11 / 99 | 99 / 99 | **11 / 99** |
| statement-form `match` on a var | cranelift / interpreter | none / none | **cranelift / interpreter** |
| statement-form `match` -> i64 | 11 / 22 | 0 / 0 | **11 / 22** |

Identical and correct for the same fixture at `aa/zz.spl` and `bbbb/zz.spl`, so
the path-dependence BOOT-15 measured is gone as a DIVERGENCE. The shared id is
still module-qualified by design — that is what the registrar writes and what the
collision checks in `mangle.rs`/`imports.rs` depend on — so it legitimately
differs between two module names; what must never differ, and no longer does, is
construction vs match within one build.

`cargo test -p simple-compiler --lib`: 4070 passed / 20 failed before (18
pre-existing + the 2 new RED), 4072 passed / 18 failed after. Failure-set diff is
empty in both directions apart from the two tests going green.

## Sync consolidation (2026-09-13, PR resolution)

Both fixes above landed independently at `mangle.rs` and, once merged, coexisted
as two redundant rewrite passes for the same `rt_enum_check_variant` folded-id
mismatch — the earlier one (`bare_enum_ids`) mutated a shared `ConstInt` vreg's
value **in place**, which can corrupt any other operand fed by the same
constant; the later one (`id_remap` / `requalify_enum_check_variant_ids`)
inserts a **fresh** `ConstInt` per call site instead. The in-place mutator was
removed during PR sync and only the fresh-`ConstInt` mechanism remains.

