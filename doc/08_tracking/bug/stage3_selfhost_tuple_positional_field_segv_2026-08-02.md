# Stage 3 self-host: bootstrap-script bug (fixed) + MIR nil-sentinel deref SEGV (fixed 2026-08-02)

- **Status:** RESOLVED — root cause was a bootstrap-script bug, fixed in
  `scripts/bootstrap/bootstrap-from-scratch.sh`. The original title of this bug
  ("pure-Simple compiler SEGVs on tuple positional field access") is **REFUTED
  as an independent defect**; see "Adjudication" below.
- **Found:** 2026-08-02, full bootstrap lane at origin `da6cac2b6a3`
- **Adjudicated:** 2026-08-02 at origin `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`
- **Severity:** was blocker — stopped Stage 3 self-host
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh` (Stage 3 argv)

## Adjudication (2026-08-02)

Two lanes independently reached different "PROVED" root causes for the same
Stage-3 failure:

- **A (2026-08-01) — script bug.** Stage 3 invoked `native-build` without the
  `--source src/compiler --source src/app --source src/lib` roots and without
  `--entry-closure` that Stage 2 (and six other `native-build` call sites) pass.
- **B (2026-08-02) — compiler defect.** This document's original body: the
  pure-Simple compiler SEGVs on tuple positional field access.

**A is correct and sufficient. B is refuted.** B's SEGV is a real observation
but it is a downstream symptom of the *same* missing `--source` roots, it is
not tuple-specific, and it is off the Stage-3 path.

### Distinguishing test (PROVED)

Base sha `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`, extracted with
`git archive` into an isolated tree (shared working copy untouched). The
Stage-3 `native-build` was replayed verbatim from
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
against the admitted Stage-2 compiler, changing one variable at a time.

| variant | extra argv | result |
|---|---|---|
| baseline (current script) | none | **RC=1**, 441,951 log lines, **3,286** `unresolved type:` errors, no binary |
| A's fix | `--source src/compiler --source src/app --source src/lib --entry-closure` | **RC=0** — `727 compiled, 0 cached, 0 failed`, 127,670,776-byte binary, 663.7 s |
| roots only | `--source ...` without `--entry-closure` | not viable — 32.6 GB RSS after 33 min with no progress output; killed. `--entry-closure` is required for closure pruning. |

Stage-3 output binary, both identity gates (PROVED): size 127,670,776 B and
`strings <bin> | grep -c "enum construction: unregistered enum"` = **2**
(self-hosted, not the Rust seed); `--version` = `simple-bootstrap 1.0.0-beta`.

The failing baseline reproduces the prior full run exactly: that run's
`stage3-native-build.log` (12.7 MB, 2026-08-01 23:14) contains 3,344
`unresolved type:` + 546 `unresolved name:` diagnostics — diagnosis A's
predicted signature.

### Corrections to the claims previously recorded here

1. **The error message quoted below is not in the failing Stage-3 log.**
   `missing parsed module for source: std.nogc_sync_mut.io.process_governor`
   does **not** appear in
   `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
   (2026-08-01 23:14): 0 occurrences of `missing parsed module`,
   `process_governor` and `signal_stubs`. The single `[ERROR] phase 3 FAILED`
   line there sits in the middle of the `unresolved type` cascade.

2. **The SEGV is not tuple-specific.** A plain array index crashes at the
   identical PC:

   ```
   fn main():
       var a: [i64] = [1, 2]
       val x = a[0]
   ```

   Tuples reach it because `t.0` lowers to `Index(base, IntLit(i))`, not
   `TupleIndex` — see `src/compiler/20.hir/hir_lowering/expressions.spl:1381`
   ("expr_dispatch.spl has no TupleIndex case at all"). Family enumerated, all
   RC=139 on the misconfigured invocation: `t.0`, `t.1`, `t.2`, tuple in `val`,
   tuple as a parameter, nested tuple `((1,2),3).0`, tuple field off a call
   result `mk().0`, and array `a[0]`.

3. **The SEGV is an artifact of the missing `--source` root.** Same compiler,
   same source file, one variable:

   | invocation | result |
   |---|---|
   | `native-build f.spl` | **RC=139 SIGSEGV** |
   | `native-build --entry-closure f.spl` | **RC=139 SIGSEGV** |
   | `native-build --source pk f.spl` | **RC=0**, 0.3 s compile |

   With the root present the same programs compile and run correctly. Value
   check against hand-computed expectations (`t=(7,9)`, `arr=[11,22,33]`,
   `n=((1,2),3)`, `take(t) -> t.1`): printed `a=7 b=9 c=33 d=3 e=4` — all
   correct, and three of five differ from the nil sentinel `3`, so this is not
   a constant-3 artifact.

   A no-tuple, no-index `print("hi")` program fails on the same misconfigured
   invocation with `AOT compile error: <invalid-heap:0x...>`, further evidence
   that the fault is loader state and not tuple lowering. B's negative control
   (`val a = entry`, "no crash") was therefore too weak: it distinguished
   crash-vs-not, but not tuple-vs-any-index, and not compiler-vs-invocation.

4. **Not a stale-binary artifact.** The SEGV reproduces identically on a
   freshly built Stage-3 binary produced from this base sha, and disappears on
   that same binary once `--source` is supplied.

## Root cause and fix

`scripts/bootstrap/bootstrap-from-scratch.sh`, Stage-3 `native-build`
invocation — added, mirroring Stage 2 verbatim:

```
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
```

before `--threads "${selfhost_jobs}"`. Mechanism: the loader fills
`module_surfaces` from the transitive `use` closure only, so directory-package
siblings that nothing explicitly imports are never loaded and
`resolve_package_sibling_symbols`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) has nothing to
register — producing the `unresolved type` cascade.

`--entry` was deliberately NOT added: it reroutes to the Rust runtime and would
void the self-host evidence. Stage 3 keeps its bare positional
`src/app/cli/bootstrap_main.spl`.

## The SIGSEGV — root-caused and FIXED 2026-08-02

The crash was real and is fixed. The mechanism recorded in the previous revision
of this section ("a raw NULL `0` reaches a slot whose emptiness is the tagged nil
sentinel `3`, so `0 != 3` passes") is **REFUTED**. There is no NULL anywhere on
this path. Measured at the fault, base sha
`aa6119dd768098aa0bb5b7b335f82f101c2e98ca`, admitted Stage-2 binary
(127,612,488 B, enum-probe = 2, `simple-bootstrap 1.0.0-beta`):

### What actually happens (PROVED)

Repro is unchanged and still RC=139:

```
fn main():
    var a: [i64] = [1, 2]
    val x = a[0]
    print(x)
```
`simple native-build f.spl` (no `--source`) -> SIGSEGV, first entry to the
function, `MirLowering.lower_dict_runtime_read+1048`, `mov (%rbx),%rdi`, rbx=0.

Three corrections, each measured:

1. **The `rt_native_neq(x, 3)` at +1025 does not guard the value that faults.**
   Its operand is `%rax`, the result of the preceding `MirBuilder.emit_call` —
   i.e. `if val get_local = get_res` (expr_dispatch.spl:850), a different local.
   The faulting value lives in `0x8(%rsp)` and is never nil-checked at all.

2. **The faulting value is the nil sentinel `3`, not NULL.** Read directly at the
   fault: `*(long*)($rsp+8) == 0x3`. `and $0xfffffffffffffff8` untags `3` to `0`,
   and the next load dereferences address 0. rbx=0 is the *untagged* sentinel, so
   rbx alone cannot distinguish `0` from `3` — that is what made NULL look
   plausible.

3. **The write is `dict_result_type = self.runtime_elem_value_type[base_local.id]`**
   (expr_dispatch.spl:842), not line 832-833. Hardware watchpoint on the slot:
   initialised at +45 to a valid `MirType.i64()` handle (`0x6b9e...`), then
   overwritten with `3` by `mov %rax,0x8(%rsp)` at +675, immediately after
   `call rt_index_get` at +670 with rdi = `self.runtime_elem_value_type`,
   rsi = `base_local.id << 3`. A dict MISS returns the sentinel; the sentinel is
   then dereferenced by `match dict_result_type.kind` at line 852.

### Why the presence guard did not stop it (PROVED, and a defect in its own right)

Line 841 guards the read with `self.runtime_elem_value_type.contains(base_local.id)`.
Aligned disassembly of that guard in the Stage-2 binary:

```
54ff9d: call rt_native_eq              ; disc(dict_result_type.kind) == disc(I64)
54ffa7: mov  0x108(%r12),%rdi          ; self.runtime_elem_value_type
54ffb6: mov  (%rbx),%rsi               ; base_local.id
54ffb9: call 704b60 <lib__common__text__contains>   ; <-- NOT rt_dict_contains
54ffde: call rt_index_get
54ffe3: mov  %rax,0x8(%rsp)            ; dict_result_type = <nil 3>
```

`.contains` on a **Dict-typed CLASS FIELD** receiver is emitted as
`lib.common.text.contains(s: text, sub: text) -> bool`, with the dict handle
passed as a text pointer. The field projection carries no HIR type and its MIR
temp is typed i64, so `receiver_is_dict` (method_calls_literals.spl:1127) stays
false and the `local_is_runtime_dict` probe misses; the call then falls into the
string-only arity-1 arm at method_calls_literals.spl:1965. That arm excludes
Array/Slice receivers (the misroute documented in its own comment at :1847) but
**never excluded Dict receivers**. The answer it returns has nothing to do with
key presence, so a MISS can report present. Same silent-wrong-answer family,
one member later.

A local-variable Dict receiver is NOT affected — control run with the same
binary, `Dict<i64, Payload>` as both a struct field and a local, hand-computed
expectations `true` then `false`: printed `present=true absent=false` for both.
The defect needs a *class* field (`self.runtime_elem_value_type` is initialised
in a different function), which is why the small probe did not show it.

### Fix

Two halves, both in pure Simple, both covering the family rather than the one
line:

1. **Receiver side** — `remember_field_projection_provenance`
   (`expr_dispatch.spl`): when a projected field's declared HIR type is
   `HirTypeKind.Dict(_, _)`, record the projection temp in `runtime_dict_locals`.
   `local_is_runtime_dict` then answers yes and every dict method on every
   `Dict`-declared struct/class field (`contains`/`has`/`contains_key`/`get`/
   `keys`/`values`/`remove`/`delete`) routes to the real dict runtime instead of
   the string arm. MirLowering alone declares ~20 such fields.
2. **Consumer side** — new `MirLowering.noted_runtime_elem_type(local) -> MirType?`
   (`expr_dispatch.spl`), which discriminates the sentinel on the RESULT instead
   of trusting key presence. All three `runtime_elem_value_type` contains+read
   pairs now go through it: `expr_dispatch.spl:842`, `expr_dispatch.spl:1435`,
   `mir_lowering_stmts.spl:1284`. A lost note degrades a type refinement to the
   pre-existing i64 default — never a crash, never a different value.

The `!= nil` test is sound *here* precisely because the slot is a class handle:
a real `MirType` is a heap pointer and can never be `3`. That property is what
the `??`-on-raw-i64 defect lacks (see below).

### Not the same defect: `??` / `lower_coalesce`

Asked whether `lower_coalesce` (`hir/lower/expr/control.rs:1181`, `x ?? d`
lowered to `BinOp::NotEq` against `Nil`) is a member of this family. **It is
not — separate defect, shared constant only.** Here the slot is a pointer domain
where `3` is unreachable as a real value, so the sentinel is unambiguous and the
bug was a *missing* guard. There the slot is `TypeId::I64`, where `3` is a legal
value, so the sentinel is *ambiguous* and no guard placement can fix it — it
needs a representation change. This fix neither helps nor hinders that one. See
`doc/08_tracking/bug/parse_family_strips_option_jit_native_2026-08-02.md`.

### Verification (PROVED)

Two Stage-3 binaries built from base sha `aa6119dd768` with the identical
`native-build` invocation (the landed Stage-3 argv plus `--entry-closure`;
without it the run burns >16 GB with zero output, matching the 32.6 GB row
above). Both `727 compiled, 0 cached, 0 failed`; both enum-probe = 2 and
`simple-bootstrap 1.0.0-beta`. The fix therefore self-compiles.

| program (all `native-build <f>` with NO `--source`) | control | fixed |
|---|---|---|
| `a[0]` array index (`f.spl`) | **RC=139 SIGSEGV, 1.31 s** | no crash (see below) |
| `d["k"]` dict read | RC=1, 0.63 s, `<invalid-heap:0x...>` | RC=1, 0.62 s, same |
| `p.x` struct field read | RC=1, 0.64 s, `<invalid-heap:0x...>` | RC=1, 0.64 s, same |
| `[1,2]` + `.len()`, no index | RC=1, 1.07 s, `<invalid-heap:0x...>` | RC=1, 1.27 s, same |
| `print("hi")` | RC=1, 1.11 s, `<invalid-heap:0x...>` | RC=1, 1.47 s, same |

The SEGV is gone and nothing else on the misconfigured path changed.

### NEWLY EXPOSED, still open: LoopDetector.reachable_from does not terminate

With the crash removed, `f.spl` no longer dies at 1.31 s — it instead runs
unbounded (killed at 110 s, 5.2 GB RSS and still climbing; a longer run reached
10 GB). This is **not** caused by the fix, it was *masked* by it: an isolation
build carrying only the consumer-side guard (no provenance change) hangs
identically, and every non-index program above is unaffected. The crash was
simply the first of two defects on this path.

Located by SIGUSR1-stop under gdb, PROVED:

```
#0 rt_dict_get
#1 rt_contains
#2 LoopDetector.reachable_from        (60.mir_opt/mir_opt/loop_detect.spl:155)
#3 LoopDetector.build_loop_info
#4 LoopDetector.detect_loops
#5 CollectionOptimization.optimize_function
#6 run_typed_pass_on_module -> pipeline_optimize -> optimize_module_for_backend
#9 CompilerDriver.optimize_mir_level -> aot_compile
```

The worklist in `reachable_from` never drains: `visited.has(cur.id)` /
`succ_map[cur.id] ?? []` keep feeding it.

**Follow-up 2026-08-02:** the membership half is now root-caused as its own
defect and filed separately —
`doc/08_tracking/bug/dict_array_contains_raw_untagged_key_2026-08-02.md`.
`.has()`/`.contains()`/`in` pass an **untagged** key to `rt_contains` while
`rt_dict_set` stores the **tagged** key (`$0x9` vs `$0x48`, PROVED by
disassembly of a tip-built compiler), so membership answers are wrong in both
directions. That is sufficient to make this worklist never drain, but the link
to this specific hang is **INFERRED, not proved**: a standalone replica of
`reachable_from` terminated correctly, so the chain still needs to be observed
inside a real compiler run. Filed here so the
fix above is not mistaken for making this invocation clean.

### The reported 900 s HANG is REFUTED (PROVED)

Same binary, same `--source`-less invocation, `/usr/bin/time`:

| program | result |
|---|---|
| `d["k"]` dict read | RC=1 in **0.67 s**, 154 MB peak RSS, `error: in-process native-build: AOT compile error in d: <invalid-heap:0x10d255a1>` |
| `p.x` struct field read | RC=1 in **0.67 s**, 154 MB peak RSS, same `<invalid-heap:0x...>` shape |

Neither hangs. Both already reach the diagnostic path — it is only the
array/dict *index* lowering that died before getting there. The 900 s
observation was most likely the `--source`-without-`--entry-closure` 32.6 GB
case recorded in the table above, misattributed.

Still open and unchanged: `<invalid-heap:0x...>` is a poor diagnostic. It does
not name the unresolvable sibling. That is the same fail-open recorded below for
`module_surface.spl:379` and stays a separate improvement request.

The secondary fail-open diagnostic noted in the original report
(`src/compiler/20.hir/hir_lowering/module_surface.spl:379`,
`missing parsed module for source: ...` with no underlying cause) remains a
valid, separate improvement request.

---

## Original report (2026-08-02, superseded by the adjudication above)

Kept verbatim for provenance; items 1-4 above correct it.

### Symptom as seen by the bootstrap

`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=llvm --full-cli`

```
Stage 2: seed -> bootstrap_main.spl                 OK (727 compiled, 0 failed)
  Stage 2: running bootstrap compiler sanity        OK
  Stage 2 native-build capability passed            OK
Stage 3: stage2 -> bootstrap_main.spl (self-host)   FAILED (exit 1)
```

Reported log excerpt:

```
[ERROR] phase 3 FAILED
error: in-process native-build: Module surface extraction error:
       missing parsed module for source: std.nogc_sync_mut.io.process_governor
```

### Reported root cause (refuted)

1. Compiling `src/lib/nogc_sync_mut/io/process_governor.spl` reports
   `missing parsed module for source: std.nogc_sync_mut.io.signal_stubs`.
2. Compiling `src/lib/nogc_sync_mut/io/signal_stubs.spl` directly segfaults
   (rc=139) during MIR lowering. `signal_stubs.spl:29-30` is
   `val sig = entry.0` / `val cb = entry.1`.

| probe | body | result |
|-------|------|--------|
| `val entry = (7, 8)` then `val a = entry`   | whole tuple | no crash |
| `val entry = (7, 8)` then `val a = entry.0` | field 0 | rc=139 SIGSEGV |
| `val entry = (7, 8)` then `val a = entry.1` | field 1 | rc=139 SIGSEGV |

### Relationship to prior state (as reported)

The 2026-07-31 verdict (`project_stage3_selfhost_blocked_2026-07-31`) is stale
and was measuring a different blocker: on 2026-07-31 Stage 3 *succeeded*
(727 compiled, 124.5 MB stage3 binary linked) and Stage 4 was the blocker, with
a parse error in `src/compiler/20.hir/hir_lowering/expressions.spl`.

The suggested link to the porter regression fixed in `284745a3cfc` /
`28adeb80809` (mis-rewriting `x.0` into `x[0]`) was inferred, never bisected,
and is now superseded: the crash is not tuple-specific at all.
