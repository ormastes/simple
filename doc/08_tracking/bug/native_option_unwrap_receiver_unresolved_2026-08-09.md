# native-build: a method call on an `Option<T>.unwrap()` receiver fails MIR lowering

- **Date:** 2026-08-09
- **Status:** **RESOLVED 2026-08-10.** The erasure was one layer further
  upstream than this doc originally concluded — not HIR type lowering but the
  **flat parser's integer type-tag registry**, which had dedicated
  `Option<T>` tags only for `i64/f64/text/bool` and collapsed every other
  inner type to bare `TYPE_OPTION` (14). Fixed by adding an Option inner-type
  specialization registry, mirroring the existing `Result<T,E>` / `Dict<K,V>` /
  `[T]` element registries. See "Resolution" at the bottom. The analysis below
  is preserved as written at investigation time; note that the "Why this was
  not fixed here" section's HIR diagnosis is **superseded**.
- **Lane:** `native-build` (AOT / MIR lowering). NOT reproducible under
  `bin/simple test` — the tree-walk interpreter resolves these receivers fine,
  so no `*_spec.spl` can observe it.
- **Fence:** `scripts/check/check-native-option-unwrap-receiver.shs`
  (on the roster in `scripts/check/check-aot-lane-fences.shs`)
- **Fixtures:** `test/fixtures/native_option_unwrap_receiver/{main,control}.spl`
- **Family:** same root mechanism as
  `doc/08_tracking/bug/native_trait_typed_return_receiver_unresolved_2026-08-09.md`
  (static devirtualization cannot recover a concrete owner name), but a
  **distinct and strictly simpler trigger** — see "Relationship to the trait
  bug", which explains why that doc's language-policy blocker does NOT apply.
  That policy call is laid out in
  `doc/02_requirements/language/type_system/native_trait_object_dispatch_options.md`.

## Symptom

```
error: MIR lowering error: unresolved method call: stat
```

Preceded in the build log by:

```
[mir-lower] WARNING: unresolved method call 'stat' lowered to const-0
placeholder (silent-null risk, Task #145)
```

## Why this matters — the SimpleOS blocker

This is the minimal form of the shape that keeps the SimpleOS hosted FAT32
mount switched off. `src/os/services/vfs/vfs_boot_init.spl:383` unconditionally
short-circuits the hosted `SharedFat32Driver` mount:

```
if true:
    serial_println("[vfs-init] hosted fat32 mount skipped: blockdevice-dispatch-codegen-bug")
    return false
```

**The marker text is stale and now misattributes the cause.** The BlockDevice
trait dispatch defect it names (C8) was CONFIRMED FIXED on 2026-07-20 by a real
QEMU boot — see the "C8-VERIFY lane" addendum at the bottom of
`doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`,
which measured `'sector_size' lowered as virtual trait call at slot 2` (a real
slot) and booted the hosted mount end-to-end with no fault storm. The skip was
deliberately kept because lifting it sets `g_vfs_initialized = true`, which
routes reads into the hosted trait path, where the *next* defect fires.

The live blocker on that hosted path is this one. `vfs_init.spl:431` and
`:580` both carry comments naming the exact call shape:

> `every disk-backed candidate below dispatches through
> g_root_fat32.unwrap().stat()`

with `g_root_fat32: Option<Fat32Core>`. That is precisely the fixture below.
Both comments currently attribute the failure to native-build "miscompiling the
`Option<SharedFat32Driver> != nil` guard"; the measurement here shows the
`.unwrap()`-receiver method call is itself unlowerable, which is a simpler and
sufficient explanation for the same site.

## Minimal reproduction (executed, both directions)

Single file, no imports, no OS, no disk. Only the `Option` hop differs between
the two fixtures.

**REPRO** — `test/fixtures/native_option_unwrap_receiver/main.spl`:

```
class Drv2:
    n: i64

impl Drv2:
    static fn new(n: i64) -> Drv2:
        Drv2(n: n)
    me fn stat(path: text) -> i64:
        self.n + path.len()

fn main():
    val o: Option<Drv2> = Drv2.new(7)
    val d: Drv2 = o.unwrap()
    println("OPTUNWRAP={d.stat(\"ab\")}")
```

`bin/simple native-build test/fixtures/native_option_unwrap_receiver/main.spl`
-> rc=1, `unresolved method call: stat`.

**CONTROL** — `control.spl`, identical minus the Option hop -> rc=0, runs,
prints `CONTROL=9`.

### Measured discriminator matrix

Every row built with `bin/simple native-build <file> -o <bin>` from the repo
root and, where it built, actually RUN.

| # | Receiver shape | Build | Run | Verdict |
|---|---|---|---|---|
| A2 | `val d: Drv2 = Drv2.new(7)` (construction site) | rc=0 | `A2=9` | PASS |
| D | `make().stat("ab")` — call return used directly | rc=0 | `D=9` | PASS |
| E | `val d: Drv2 = make()` — call return into annotated local | rc=0 | `E=9` | PASS |
| B | `val d: Drv2 = o.unwrap()` where `o: Option<Drv2>` | rc=1 | — | **FAIL** `unresolved method call: stat` |
| C | same as B but `Drv2` imported from another module | rc=1 | — | **FAIL** (identical) |

What this rules out, by measurement rather than by argument:

- **Not cross-module resolution.** B is single-file and fails; A2 is
  single-file and passes. C (cross-module) fails identically, so the module
  boundary changes nothing.
- **Not "a call-returned receiver".** D and E both put a *call return* in
  receiver position and both pass. The distinguishing property is that their
  declared return type names a concrete class.
- **Not the method names.** `stat`/`open`/`read` are inherent methods on a
  plain class here; A2/D/E call the same `stat` and pass.
- **Not fixed by an annotated intermediate `val`.** B already uses the
  documented erased-receiver workaround (`.claude/rules/language.md`,
  "Chained methods on erased receivers") and still fails. The annotation is
  present in source and simply is not consulted.

## Root cause

Static devirtualization is the only dispatch mechanism the native lane has.
MIR's `Unresolved` arm recovers the receiver's **concrete owner name** from
`struct_value_syms` and rewrites the call to `"{Owner}::{method}"`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, Unresolved
arm; the sibling trait bug doc walks this block in detail).

The `Option.unwrap()` lowering already knows it must carry struct identity
across the unwrap, and does so — but only by **propagating from the receiver**
(`method_calls_literals.spl:665-666`):

```
if self.struct_value_syms.contains(receiver_local.id):
    self.struct_value_syms[result_local_uw.id] = self.struct_value_syms[receiver_local.id]
```

The receiver here is the `Option` handle, which is a boxed enum payload and not
a construction site, so it carries no `struct_value_syms` entry of its own and
the propagation misses. The unwrap result therefore reaches the Unresolved arm
with **no owner name at all**, no fallback matches, and lowering hits
`self.error("unresolved method call: {method}", nil)`.

The obvious second source of truth is the Option's own type ARGUMENT —
`Option<Drv2>` names exactly one concrete type. That is recovered a few lines
earlier by `option_inner_hir_type_for_local`
(`method_calls_literals.spl:321-331`), whose result is used to pick the MIR
result *type*.

**Measured, not assumed:** an instrumented build of the B fixture (temporary
`eprint` in that arm, since reverted — the file is byte-identical to HEAD in
lines 560-700) printed:

```
[OPTPROBE] unwrap arm inner_name='' inner_nil=false local_ty_nil=false recv_has_sym=false
[OPTPROBE] inner kind = OTHER
```

So: the arm IS reached; `option_inner_hir_type_for_local` DOES return an inner
type (`inner_nil=false`); the receiver has no struct sym (`recv_has_sym=false`,
confirming the propagation above misses); **but the recovered inner type is not
`HirTypeKind.Named`** — it matched neither `Named`, nor `Optional`, nor `Int`,
falling to the wildcard. `Named(symbol, args)` is the *only* HirTypeKind
variant that carries a user-defined type identity
(`src/compiler/20.hir/hir_types.spl:783+`).

**Conclusion: the concrete type argument of `Option<Drv2>` has already been
erased in HIR, before MIR lowering ever runs.** The annotation survives as far
as "there is an Optional here" but its payload identity is gone.

## Why this was not fixed here

The tempting MIR-local fix — in the `.unwrap()` arm, when the receiver carries
no struct sym, fall back to the Option's inner type name — was written and
executed. **It is inert**, because of the finding above: there is no name left
in the inner type to read. Landing it would have added dead code that looks
like a fix. It was reverted; the working region of
`method_calls_literals.spl` is byte-identical to HEAD.

The real fix belongs in HIR type lowering (`src/compiler/20.hir/hir_lowering/`,
the `Optional(inner)` construction path), which must preserve
`Named(symbol, args)` for the inner type instead of erasing it. That is a
change to a load-bearing shared representation with broad blast radius across
every `Option<T>` consumer, and correctly scoping it needs a deliberate pass
rather than a guess appended to this investigation.

## Relationship to the trait bug (why this is NOT a duplicate)

`native_trait_typed_return_receiver_unresolved_2026-08-09.md` documents the
same *mechanism* (owner-name recovery fails -> `unresolved method call`) and
explicitly declines to fix it because its trigger, a **trait-typed** receiver,
raises a language-policy question: with two or more impls of a trait the
concrete type is genuinely unknowable, so a single-impl special case would
create a silent capability cliff.

**That blocker does not apply here.** This defect's receiver is typed by a
concrete **class**, via an `Option`'s single type argument. There is exactly
one possible answer, no impl-count ambiguity, and no policy question — only a
representation gap. It is therefore soundly fixable on its own, and should not
be closed as a duplicate of the trait bug or made to wait on that policy call.

## Fix recipe

1. `src/compiler/20.hir/hir_lowering/` (the `HirTypeKind.Optional(inner)`
   construction path) — preserve the inner type as `Named(symbol, args)`
   rather than erasing it to the wildcard kind observed above. Verify with the
   same one-line probe: the `[OPTPROBE] inner kind` arm must report `Named`.
2. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:665-666` —
   extend the existing propagation with an `elif` that, when the receiver has
   no `struct_value_syms` entry, resolves the inner `Named` symbol via
   `self.symbols.get_symbol_raw(sym.id)` and registers `.name` on the unwrap
   result local. (This half is already written and proven to compile; it is
   only waiting on step 1 to have data to read.)
3. Re-run the fence; it flips itself to the FIXED verdict automatically when
   the repro builds and prints `OPTUNWRAP=9`.
4. Then revisit `src/os/services/vfs/vfs_boot_init.spl:383` — lift the
   `if true:` skip, boot x86_64 QEMU with NVMe, and confirm the hosted mount
   completes. Regardless of that, the skip's marker string
   `blockdevice-dispatch-codegen-bug` should be renamed: it names a defect that
   has been fixed since 2026-07-20 and misdirects every reader who follows it.

## Verification / attribution

- Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
  29577536 bytes, 2026-08-09 04:50, which **self-reports as the Rust bootstrap
  seed**. However `native-build` drives the **pure-Simple** `src/compiler/**`
  lowering: every `[mir-method-call] ...` and `[mir-lower] WARNING ...` line
  quoted above is emitted by
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, and the
  temporary `eprint` added to that `.spl` file appeared in the build output —
  a direct positive proof that the `.spl` source is live on this lane. So
  these results are evidence about the pure-Simple MIR lowering, **not** about
  the seed's own codegen.
- The Rust seed (`src/compiler_rust/**`) was not modified. Its own separate
  `DUCK_DISPATCH_UNSUPPORTED_SLOT` sentinel path (the mechanism behind the
  original C8 and the FileSystem-trait sentinel) has **no counterpart in
  `src/compiler/**`** — a `/usr/bin/grep` for `DUCK_DISPATCH_UNSUPPORTED_SLOT`
  over `src/compiler/` returns zero hits — so the two lanes fail differently
  and results from one do not transfer to the other.
- Fence sabotage-proved in both directions: breaking the control's expected
  value produced `FAIL — control fixture built but produced the wrong value`;
  making the repro build while printing a wrong value produced `FAIL —
  Option-unwrap receiver now FAILS OPEN`. Both fixtures restored, fence
  re-verified PASS.

## Related

- `doc/08_tracking/bug/simpleos_filesystem_trait_dispatch_sentinel_2026-07-20.md`
  — the seed-lane FileSystem-trait sentinel, the other thing lifting the mount
  surfaces. Still OPEN.
- `doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`
  — C8 and its six investigation lanes; C8-VERIFY records the BlockDevice fix.
- The `#UD` (`ud2`) trap being treated as a recoverable `RIP+=2` event by the
  freestanding fault handler was hardened in the C8-CLOSE lane but is the
  reason this whole family historically presented as wild-jump storms rather
  than clean traps.

## Resolution (2026-08-10)

### The actual erasure point

The investigation above correctly proved that MIR received `Optional(<not
Named>)` and correctly concluded the identity was gone before MIR ran. It
placed the loss in `20.hir/hir_lowering/types.spl`. It is in fact one layer
earlier, and that file was innocent: `lower_named_kind` already builds a real
`HirTypeKind.Optional(inner)` from `Named("Option", [T])` — it simply never
received a `T`.

`src/compiler/10.frontend/core/parser.spl`, the `Option<T>` branch of
`parser_parse_type_impl`, tests the inner tag against exactly four dedicated
flat tags and otherwise discards it:

```
if type_name == "Option":
    if inner_type == TYPE_I64:   return ...(TYPE_OPTION_I64)
    if inner_type == TYPE_F64:   return ...(TYPE_OPTION_F64)
    if inner_type == TYPE_TEXT:  return ...(TYPE_OPTION_TEXT)
    if inner_type == TYPE_BOOL:  return ...(TYPE_OPTION_BOOL)
    return parser_absorb_optional_suffix(TYPE_OPTION)   # <-- identity dropped
```

The postfix-`?` shorthand branch (`Drv2?`) had the identical four-primitive
chain and the identical `TYPE_OPTION` fallback. The flat AST is an integer-tag
representation with no room for a type argument, so `Option<Drv2>` and `Drv2?`
both arrived at the bridge as the bare tag 14, which
`_FlatAstBridge/convert_nodes.spl` faithfully rendered as the argless
`Named("Option", [])`. HIR then produced `Optional(Any)` — the `inner kind =
OTHER` the probe measured. The comment at
`35.semantics/lint/option_me_call.spl:35` had already recorded this exact gap
("there is no `TYPE_OPTION_<named>` encoding") without connecting it to this
failure.

### The fix

The repo already had the answer three times over: `Result<T,E>`, `Dict<K,V>`
and `[T]` all solved the same "no room in an integer tag" problem with a
side-table registry whose id is encoded into an out-of-band tag range. Option
now has the fourth, modelled directly on the single-argument array-element one.

1. `src/compiler/10.frontend/core/types.spl` — `TYPE_OPTION_GENERIC_BASE`
   (300..500, the free gap below `TYPE_UNION_BASE`), `is_option_generic_tag`,
   `option_generic_tag_to_id`, `option_generic_type_register`,
   `option_generic_type_get_inner`, pool clear, exports.
2. `src/compiler/10.frontend/core/parser.spl` — both the `Option<T>` generic
   branch and the postfix-`?` branch register a **named-base** inner tag
   instead of collapsing to `TYPE_OPTION`. Deliberately scoped to
   `>= TYPE_NAMED_BASE` inners: that is exactly the defect, and it leaves every
   other Option spelling on its existing path.
3. `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` — decode the new
   tag range into `Named("Option", [<inner>])`, placed with the sibling
   dict/result/tuple/array checks before the `>= TYPE_UNION_BASE` catch-all.
4. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` — the
   `elif` the recipe called for, now with real data to read: when the receiver
   carries no `struct_value_syms` entry, recover the owner name from the
   Option's inner `Named` symbol via `symbols.get_symbol_raw(...).name` and
   register it on the unwrap-result local, so the Unresolved arm devirtualizes.

Steps 1-3 are the fix; step 4 alone is the inert change this doc already
documented as reverted.

### Evidence

- `sh scripts/check/check-native-option-unwrap-receiver.shs`
  -> `PASS — 2 fixtures checked: control=CONTROL=9, repro=OPTUNWRAP=9
  (Option-unwrap receiver resolves correctly on the native lane)`.
  The repro now BUILDS AND RUNS with the correct value; it previously passed
  only via the known-open `unresolved method call` branch.
- **The fence was tightened, not just re-run.** The `KNOWN-OPEN` acceptance
  branch is deleted: a build failure carrying `unresolved method call` is now a
  hard `FAIL — REGRESSION`, and any other build failure is a hard FAIL too. The
  fail-open direction (builds, prints a wrong value) remains a hard FAIL. Exactly
  one outcome passes, so the fence is closed in both directions.
- **Sabotage-proved.** Disabling the parser registration alone
  (`if inner_type >= TYPE_NAMED_BASE` -> `if false`) reproduced the original
  failure through the tightened fence:
  `FAIL — REGRESSION: the Option-unwrap receiver is unresolvable again
  ('unresolved method call')`. Restored byte-identical (verified by `diff -q`),
  fence re-run -> PASS.
- Regression specs (interpreter lane, `bin/simple test`, real verdict lines):
  - `test/01_unit/compiler_core/parser_option_coverage_spec.spl` executed=29
    passed=29 failed=0
  - `test/01_unit/compiler/qualified_result_option_no_import_spec.spl`
    executed=6 passed=6 failed=0
  - `test/01_unit/language/dict_get_option_match_spec.spl` executed=2 passed=2
    failed=0
  - `test/01_unit/language/option_i64_value3_sentinel_spec.spl` executed=5
    passed=5 failed=0
- `parser_option_coverage_spec.spl` initially went 27/29. **Both failures were
  the spec asserting the defect**: `Option<CustomType> returns TYPE_OPTION` and
  `CustomType? returns TYPE_OPTION` (`expected 300 to equal 14`). They were
  rewritten to assert the inner type is PRESERVED — a strictly stronger oracle
  than the equality they replaced, not a loosened one.
- `sh scripts/check/check-native-trailing-default-param.shs` FAILS on this tree
  (garbage trailing default values, e.g. `times=123328077358976`). **Measured
  pre-existing, not caused by this change**: re-running it with both parser
  registrations disabled produced the identical FAIL. Unrelated lane; not
  investigated here.

### Attribution

`bin/simple` self-reports as the Rust bootstrap seed, but every file changed
here is pure-Simple `src/compiler/**` driven by `native-build`, and the
sabotage/restore cycle above is direct positive proof that these `.spl` sources
are the ones live on that lane. The Rust seed (`src/compiler_rust/**`) was not
touched, and its own lane is unaffected and unmeasured.

### Follow-on still open

`src/os/services/vfs/vfs_boot_init.spl:383` still carries the unconditional
`if true:` skip and the stale `blockdevice-dispatch-codegen-bug` marker. The
compiler defect that actually kept it switched off is now fixed, so lifting the
skip is newly viable — but that requires a real x86_64 QEMU + NVMe boot to
claim, which was NOT done here and must not be assumed from this fix alone.
The sibling `native_trait_typed_return_receiver_unresolved_2026-08-09.md`
remains OPEN and is genuinely blocked on its multi-impl policy question; this
fix does not address it, exactly as that doc's "Relationship" section predicted.
