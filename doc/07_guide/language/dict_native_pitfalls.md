# Dict Pitfalls Under Native Codegen

> **RESOLVED 2026-08-09 (re-verified).** The two headline defects this doc was
> originally written for — `Dict.len()` always returning `-1`, and `.get(k)`
> on a hit being corrupt for struct/class/enum value types — are **fixed** and
> were re-confirmed fresh today via real JIT execution (`SIMPLE_LOG=cranelift_jit=debug
> bin/simple run`, confirmed by `cranelift_jit::backend` log lines and
> `PROT_EXEC` code-page mmaps in `strace`, not a silent interpreter fallback).
> Two independent probes (`d.len()` on a 2-entry then a 3-entry `{text: i64}`
> dict; `.get()` on a `{text: Payload}` struct-valued dict with two distinct
> keys) both returned correct, key-differentiated results — `LEN_MARKER=2` /
> `LEN3_MARKER=3`, and a sabotage/negative-control probe fetching the
> *second* inserted struct returned that struct's own fields (`999`/`zzz`),
> not the first's or a stale/corrupt value. Fix commits: `.len()` routing fix
> landed 2026-08-01 (native ELF `8fdc21c67b5`); `.get()` hit-decode fix is
> `7e83e92ce31` ("fix(mir): decode Dict.get() exactly like the d\[k] index
> read"). Both live in the pure-Simple MIR lowering
> (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` for
> `.len()`, `expr_dispatch.spl` for `.get()`), not the C runtime — the
> underlying `rt_dict_len`/`rt_dict_get` runtime entry points were already
> correct; the bug was in the MIR lowering's receiver-type routing that fed
> them. **The `f64`-value `.get()` miss gap and the class-field `d[k]`
> bracket-read array-value segfault (see Truth table below) remain open** —
> only the two headline defects named in this doc's title are resolved.

Two native-codegen defects **used to** make common `Dict` operations silently
wrong or crash-prone (see the RESOLVED note above — both are now fixed).
Historically they were **native-only** — the interpreter and the Rust seed
both behaved correctly, so a seed build or an interpreter-mode test run
**could not** catch either bug; only a native build/run exercised the broken
paths. The truth table below still lists the OTHER, still-open native-only
gaps (`f64`-miss, class-field array bracket-read) for which that caveat still
applies — treat "seed-build verified" or "interpreter test green" as no
signal for those remaining rows.

Both syntaxes are affected: `Dict<K, V>` **and** the brace shorthand
`name: {K: V}`. A grep for `Dict<` alone misses roughly a third of the real
exposure — always also search for `: {`-style dict declarations.

## Truth table

> **UPDATED 2026-08-01.** Two rows changed. `.len()` no longer reproduces as
> `-1` — measured `2` for both a local `Dict<text,i64>` and a dict passed as a
> function parameter, on a native ELF built from `8fdc21c67b5`. And the
> `.get()` MISS row is now correct for `i64` and `bool` value types (fix:
> `dict_get_preserve_flat_nil`, see
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`).
> **`text`-valued dicts are still broken on a miss** — the `contains_key(k)` +
> `d[k]` replacement below is still mandatory for those.

> **RE-VERIFIED 2026-08-07 on the current working tree, real JIT execution
> (`bin/simple run`, Cranelift JIT — the native-codegen lane; see
> `.claude/rules/testing.md` "run and test are DIFFERENT ENGINES"; confirmed
> via `cranelift_jit::backend` log lines, not a silent interpreter fallback).
> `d.len()` (local + parameter), `.get()` hit for `i64`/`text`/struct, and
> `.get()` miss for `i64`/`text` (both `== nil` and `?? default`) all measured
> **correct**. The `text`-miss row above is now STALE: `guardable_value_type`
> at `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:991` already
> includes `mir_type_is_str`, so `dict_get_preserve_flat_nil` guards `text`
> the same way it guards integers — the "still broken" note predates that
> guard landing. Root cause for every row above, in one place: `rt_dict_get`
> (`src/runtime/runtime_native.c:7137`, flat-Option ABI) returns the nil
> sentinel `RT_NIL == 3` on a miss; `decode_runtime_value`
> (`expr_dispatch.spl:741`) has per-type arms that TRANSFORM the raw word
> (`>>3` for ints, `rt_interp_cstr` for text) and would destroy that sentinel
> on a miss; `dict_get_preserve_flat_nil` (`expr_dispatch.spl:833`) routes the
> sentinel around the transform via a branch-and-select, gated by
> `guardable_value_type` (`expr_dispatch.spl:991`, integer or str). Struct/
> enum/array/dict decode arms need no guard — their arm already passes the raw
> word through untouched, so nil survives for free.
>
> **One row was claimed still genuinely broken: `.get()` miss for `V = f64`.**
> **RE-CHECKED 2026-08-08 — the claim, on inspection, splits into two separable
> pieces: the symptom is real (unverified today, but plausible from the code),
> the ABI rationale for it is WRONG, and the "confirmed live" evidence behind
> the 2026-08-07 entry does not hold up.**
>
> **The ABI-capacity claim is false under the current representation.**
> `guardable_value_type` (`expr_dispatch.spl:1053`) does exclude
> `mir_type_is_f64` — that part is accurate — but the stated reason ("the flat
> `Option<f64>` ABI has no spare bits to carry a sentinel alongside a real
> float payload") does not match `src/runtime/runtime_native.c`. F64 values
> that enter the tagged/boxed representation are **heap-boxed**
> (`rt_value_float`, line 2086: `malloc`'d `RtCoreFloat`, tag `RT_VALUE_TAG_HEAP
> = 0x1`, low 3 bits `001`) with a legacy inline fallback only on OOM
> (`RT_VALUE_TAG_FLOAT = 0x2`, low 3 bits `010`). `rt_core_nil()` is
> `RT_VALUE_TAG_SPECIAL = 0x3`, low 3 bits `011`. No legitimately-tagged f64
> word — boxed or legacy-inline — can equal `3`: the three representations
> occupy disjoint low-3-bit classes (`001`/`010`/`011` are all distinct, and a
> malloc'd pointer's low 3 bits are `000` before the tag OR, an inline float's
> are forced to `010` by `(bits & ~7) | 2`). `rt_value_as_float(3)` does not
> crash or corrupt on the sentinel either — `rt_core_as_heap_float` rejects
     it as non-heap-tagged, falls through to the legacy-inline decode, and
> returns a harmless `0.0`. So a `raw == 3` guard, structurally identical to
> the one `dict_get_preserve_flat_nil` already applies for `i64`/`text`, is
> tag-space-safe for `f64` too. **A boxed/side-channel discriminant is not
> required — the existing tag bits already are the spare bits.** If a fix is
> attempted, note one landmine found while reading `dict_get_preserve_flat_nil`:
> its nil lane does `emit_cast(nil_raw=3, merge_type)`, and for `f64`
> `merge_type` is `f64` — casting the *integer* `3` to `f64` produces `3.0`,
> not the bit pattern `3`. That lane needs an `emit_bitcast` (or an i64-typed
> merge with a bitcast on the value lane) or the guard will compare a real
> `3.0` against a real `3.0` and misfire on a *stored* `3.0`. A one-line
> predicate addition to `guardable_value_type` alone is not sufficient.
>
> **The "confirmed live" 2026-08-07 evidence does not establish what it
> claimed.** Both that entry and this doc's own re-verification note above it
> ran `bin/simple run` against `bin/release/x86_64-unknown-linux-gnu/simple` —
> which prints "this Rust-built Simple binary is a bootstrap seed only" at
> every invocation. That banner is the tell: it is the **Rust seed**, not the
> pure-Simple self-hosted binary. `guardable_value_type` and
> `dict_get_preserve_flat_nil` live in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
> — pure-Simple source, part of the self-hosted compiler's MIR lowering, which
> the Rust seed's own Cranelift backend (`src/compiler_rust/compiler/src/codegen/`)
> does not execute. So a probe run through the seed cannot exercise the guard
> gap being described at all, in either direction. Session 2026-08-08 tried to
> independently confirm real JIT engagement on the seed via a different
> route (`strace`-based code-allocation and canary-divergence checks, below)
> rather than the log route. **Correction:** this session's earlier claim
> that no `env_logger`/`tracing_log::LogTracer` bridge exists, and that
> `log`-crate-emitted lines are therefore physically unobtainable, is
> REFUTED — `src/compiler_rust/driver/src/log.rs:8-9` sets up
> `EnvFilter::try_from_env("SIMPLE_LOG").or_else(RUST_LOG)`, and
> `tracing-subscriber` is declared without `default-features = false`
> (`driver/Cargo.toml:52`), so `Cargo.lock:5440` shows it pulls in
> `tracing-log`, which IS the bridge. The prior claim was reached by
> grepping only the literal strings `env_logger`/`LogTracer` and missing this
> real bridge. **Prior sessions' log-verified `cranelift_jit::backend`
> evidence of real JIT engagement STANDS** — it is not invalidated by this
> doc. `strace -e
> trace=mmap,mprotect` across five minimal f64 probes on the seed showed no
> anonymous RWX/RX code allocation at all, and three previously-"JIT-only"
> divergent-behaviour canaries (array-OOB-miss text leak, `list.get` `<<3`
> shift, `.filter()`) that used to distinguish JIT from interpreter on this
> exact binary all now print the CORRECT (interpreter-matching) answer in
> both `SIMPLE_EXECUTION_MODE=jit` (default) and `=interpret` — so those
> canaries no longer discriminate either, and no working discriminator was
> found this session. **Net: the f64-miss gap's current status on the
> pure-Simple/self-hosted lane is UNVERIFIED, not confirmed-broken** — the
> blocker is verification access to that lane, not the ABI.
>
> **Why the pure-Simple lane could not be reached directly either.** The
> repo-managed `bootstrap/stage{1,2,3}/simple` binaries are byte-identical
> (`md5sum` matches across all three, including
> `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`) and expose only
> `compile --format=smf` and `native-build` — no `run` subcommand, so they
> cannot execute a probe directly. `native-build` on the minimal f64 probes
> segfaulted (rc 139) before producing an ELF, consistent with the open
> stage-3 native-build instability tracked elsewhere in `doc/08_tracking/bug/`.
> No bootstrap rebuild was performed (out of scope per task instructions).
>
> Tracked with the bool case in
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`.
> Spec coverage: `test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl`
> (passes under the interpreter always — see that file's lane-coverage
> warning, now also flagged as unverified rather than confirmed for the
> native/JIT lane; the interpreter itself has never been reported broken
> here).
>
> **Recommended action, until someone can run a probe through the actual
> pure-Simple `bin/simple run`/JIT lane:** keep treating `.get()` miss for
> `V = f64` as unsafe and use the `contains_key(k)` + `d[k]` replacement below
> — the workaround costs nothing whether or not the gap turns out to still be
> real, and the tag-bit analysis above means a guard fix (with the
> `emit_bitcast` correction noted) is a plausible, low-risk fix once someone
> can verify it lands correctly on the JIT lane.

| Operation | Native codegen result | Safe to use? |
|---|---|---|
| `d.len()` / `d.length()` | correct count since 2026-08-01 (measured: local **and** function parameter). The old **-1** does not reproduce; struct-field receivers remain unmeasured | yes for locals/params |
| `d.get(k)` — miss, `V` = `i64` / `bool` | correct `nil` since 2026-08-01 — `== nil` true, `?? default` fires | yes |
| `d.get(k)` — miss, `V` = `text` | correct `nil` — re-verified 2026-08-07 on current source (see re-verification note above); the row title below was stale | yes |
| `d.get(k)` — miss, `V` = `f64` | **REPRODUCES — measured 2026-08-17, no longer unverified.** A miss decodes to `0.0` with `== nil` false and `??` not firing; **and, in the opposite direction, a STORED `3.0` is reported as nil** (`== nil` true, `??` fires). `d[k]` returns `3.0` correctly, so the value is stored fine and only `.get()`'s nil guard is broken. Measured interpreter-vs-Cranelift-JIT on the seed with a confirmed `[jit-addr]` engine witness. This is exactly the `emit_cast(3 → f64) == 3.0` landmine predicted in the note above — so a fix needs a **bitcast**, not just adding f64 to `guardable_value_type`. Standing guard: `scripts/check/check-dict-engine-differential.shs` (case `text_f64_local`). Record: `doc/08_tracking/bug/native_dict_f64_get_nil_sentinel_collides_with_stored_3_2026-08-17.md` | **NO** |
| `d.get(k)` — hit, `V` = `bool`, value `true` | correct since 2026-08-01 (`.get()` on a bool dict now returns the raw 3-state word) | yes |
| `d.get(k)` — hit, `V` = `i64` / `text` | correct since `7e83e92ce314` (was `7`→`56`) | yes |
| `d.get(k)` — hit, `V` = struct/class/enum | correct since `7e83e92ce314` (was a segfaulting corrupt `Option`) | yes |
| `d.get(k).?` | **conflates a present `0` with empty** — reports empty for a stored zero | **NO** |
| `d[k]` indexed read — **miss** | **`0`**, silently — no miss signal at all | **NO** |
| `d.contains_key(k)` | correct | yes |
| `d.keys()` | correct | yes |
| `d[k]` indexed read — hit | correct | yes |
| `Some(d[k])` manual wrap | correct — round-trips through `.unwrap()` and `Option`-typed params | yes |

> **CHANGED 2026-07-28 — the MISS row was previously WRONG.** This table used to say
> `d.get(k)` on a miss was "correct, `nil`". It is not: a miss returns the **zero value**
> of the dict's value type, so a missing key is indistinguishable from a present zero.
> **Measured natively for `i64`, `bool`, and `text`** (standalone native ELF, no
> interpreter). Several 2026-07-27 sweeps reviewed call sites against the old
> "miss path is safe" assumption and **need revisiting**. Struct/class/enum value types
> were **not** measurable (any module-level `struct` makes native-build fail with
> `MIR module has no functions`); static reading says they preserve nil, but that is
> unverified. Details:
> `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`.
>
> Cause: `rt_dict_get` returns the nil sentinel `3` on a miss, and the MIR lowering
> decodes it as data with no nil guard — `3 >> 3` → `0` for integers, `3 == 11` → `false`
> for bools, `rt_interp_cstr(3)` → `NULL` for text. Only the struct/default decode arm
> passes the sentinel through untouched. This is **pre-existing**, not caused by
> `7e83e92ce314` — it was first sighted as `scratchpad/dict_native_report.md` item 15
> and never filed until now.

> **NEW 2026-08-08 — class-field `d[k]` bracket-read SEGFAULTs for array
> value types; `contains_key`/`keys().len()` on the same field do not.**
> Investigated a lane report that `contains_key(self.local_tuple_types,
> sym.id)` (a `Dict<i64,[HirType]>` **class field**) returned `false`
> immediately after a same-scope `self.d[k] = v` insert. Minimal
> `native-build` reproduction with a `class Holder: d: {i64: [i64]}` field:
> `contains_key(k)` → `true` (correct) and `.keys().len()` → `1` (correct)
> right after insert. But adding `val readback: [i64] = self.d[k]`
> immediately after the same insert **SEGFAULTs** (rc 139, no crash when the
> identical dict is a local/non-field variable — `contains_key` +
> bracket-read both succeed there). So the documented-safe replacement
> pattern (`contains_key(k)` then `d[k]`) is only half-safe for a
> **class-field** dict whose value type is an array: the membership-check
> half is fine, the index-read half crashes. Interpreter (`bin/simple test`)
> is correct for all three operations on the same fixture — this is
> native-codegen only. Spec:
> `test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl`.
> Full writeup: `doc/08_tracking/bug/dict_class_field_contains_key_after_insert_2026-08-08.md`.
> The original lane's `contains_key` failure was NOT reproduced by this
> investigation and remains unexplained — see that doc for what was ruled
> out.

## Replacements

- **Membership check** — use `contains_key(k)`, never infer it from `.get(k) != nil`.
  A miss returns the zero value, so `.get(k) != nil` is **true for every key**,
  present or not.
- **Miss / default handling** — `.get(k) ?? default` and `val Some(x) = .get(k) else:`
  both take the present-value branch on a miss. Test `contains_key(k)` first and
  supply the default yourself. `.get(k).?` is also unsafe — it reports empty for a
  stored `0`. **Exception, re-verified 2026-08-07:** for `V = i64`, `bool`, or
  `text`, `.get(k)`'s miss handling (`== nil`, `?? default`) is correct on the
  current native/JIT lane — the guard above is still the right default for
  everything else (struct/enum/array/dict decode is unmeasured on a miss; `f64`
  is unguarded in source and unverified at runtime on the self-hosted lane —
  see the 2026-08-08 note above — so treat it as unsafe).
- **Count** — `d.len()` is correct again as of 2026-08-01 for local and
  parameter receivers; the `d.keys().len()` workaround is no longer required
  for those, though it stays correct. Struct-field receivers have **not** been
  re-measured, so leave existing `keys().len()` calls on fields alone until
  they are.
- **Value fetch** — use `contains_key(k)` then index-read `d[k]`, not `.get(k)`.
- **Need an `Option`** — wrap the index read yourself: `Some(d[k])`, not `.get(k)`.

## Examples

BAD:

```simple
if d.len() == 0:
    return

val entry = d.get(name)
if entry != nil:
    print entry.unwrap().field
```

GOOD:

```simple
if d.keys().len() == 0:
    return

if d.contains_key(name):
    val entry = d[name]
    print entry.field
```

BAD (Option needed downstream):

```simple
val maybe: Tr? = d.get(key)
```

GOOD:

```simple
val maybe: Tr? = if d.contains_key(key): Some(d[key]) else: nil
```

## `.set()` conversion status (census 2026-07-31)

`.set()` is the write-side member of this family: it silently DROPS the insert
under native codegen. Always write `d[k] = v`.

Converted and landed: **35 sites** — `9d6527489f9d` (std.diag, 7) and
`e46120dfdf6c` (28 across 7 files). Evidence that `d[k] = v` is correct in the
interpreter is a sentinel probe on `diag_spec.spl`: 14/14 both before and after
the conversion, but 13/14 (`counter bytes_sent = 0`) when one converted write was
deliberately mis-keyed. That step matters — "green before and after" alone cannot
distinguish a correct change from a spec that never executes the line.

**The family is NOT closed. 71 verified builtin-`Dict` `.set()` sites remain**
across 19 files (12 under `src/`, the rest test-only). Highest-priority live
clusters: `security/types.spl` (12 — `keys`/`sessions`/`key_handles`/
`accepted_signatures`), `security/auth/context_propagation.spl` (12, three
concurrency-tier copies), `security/kms_provider.spl` (4),
`app/interpreter/core/environment.spl` (2 — `Scope.bindings`, the interpreter's
own variable define/set path).

**Do not grep-and-convert blindly.** A bare `.set(` sweep is overwhelmingly false
positives: `SdnRow` (744+ sites — its own `me set` already does `self.fields[k]=v`
internally), the `Persistent*` map/trie/set family (~1,000+, each with its own
`fn set`), array `[T].set(i, v)`, `Bitset`/`RowBitmap`/`FixedArray`, and a
*custom* `Map<K,V>` struct at `src/lib/nogc_sync_mut/src/map.spl` that is not a
builtin `Dict` at all. Resolve each receiver's declared type before touching it.

Two things found during the census that are NOT this bug:
- `src/app/ui.mcp/tools.spl:87` and `test/03_system/os/file_io_spec.spl:81` call
  `.set()` on `SdnDocument`, which has **no `.set` method** — stale callers
  against a refactored API.
- `src/compiler_rust/lib/std/**` holds ~54 more sites but is **dormant** (zero
  importers). Do not fix it; also do not delete it, as it carries unique Lean
  formalization files.

Reachability notes, so later readers don't over-rate two of the converted
clusters: `VhdlConstraintChecker`/`TarjanSCC` in `70.backend/vhdl_constraints.spl`
is **never constructed by the live `--backend vhdl` pipeline** — only by its own
unit spec. And `app/interpreter/helpers/imports.spl` is **entirely orphaned**: no
`.spl` file imports it, and its `Module__new` receiver has no `struct Module`
anywhere in live code (the real loader is `interp.load_module` in
`module/evaluator.spl`). Converting them was harmless, but neither was a live
production defect.

## Background

- `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md` —
  `.get()` on a MISS returns the zero value of `V` instead of `nil`; `== nil`,
  `??`, and `.?` all take the wrong branch. Silent wrong answer, no crash.
- `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md` —
  `.len()` always returns -1 under native codegen.
- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
  — `.get()` on a hit returns a corrupt Option (struct values) or a
  still-boxed value (`i64` values).
- `doc/09_report/dict_get_struct_value_exposure_sweep_2026-07-27.md` — sweep
  of 193 CRITICAL call sites across the repo; documents the `Dict<`-only
  grep undercount.

These defects caused a multi-hour misdiagnosis during 2026-07-27 stage-4
bootstrap debugging: a `.len() < 0` guard was mistaken for a legitimate
signal, an unrelated `while d.len() < cap` loop ran unbounded, and a
`functions.len() < 0` "partial module" heuristic fired on every module.
