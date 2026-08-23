# Self-host HIR cache encoding segfaults in `hc_enc_hir_type` (2026-08-22)

Status: OPEN (P1 compiler correctness blocker)

## Reproduction

Using the freshly admitted Stage 2 compiler from commit `b22c425c43e`, run a
one-file native build with the default frontend cache enabled. The source only
declares and calls `rt_mem_snapshot_open`; its contents are not required to
trigger the crash. The compiler reaches HIR post-diagnostics and exits 139.

## Measured backtrace

```text
hc_enc_hir_type
hc_enc_hir_symbol
hc_enc_symbol_table
hc_enc_hir_module
hir_module_encode
hir_cache_store
CompilerDriver.lower_and_check_impl
CompilerDriver.compile
```

The same admitted compiler reaches the snapshot-open fail-closed diagnostic
when `SIMPLE_MEM_SNAPSHOT_FILE` is set, before cache storage. Stage 3 recovery
sets `SIMPLE_FRONTEND_CACHE=0`, so this cache crash is distinct from the
snapshot ABI defect fixed by `b67c3e5a881` and from the open Stage 3 RSS issue.

## Next evidence

Reproduce after the snapshot ABI fix has been rebuilt into Stage 2, inspect the
`HirType` value entering `hc_enc_hir_type`, and compare generated
`hc_enc_symbol_table` / `hc_dec_symbol_table` fields with `SymbolTable` before
changing cache format or promotion ownership.

## 2026-08-23 -- classification and faulting instruction (VERIFIED)

Reproduced twice, deterministic, on
`/mnt/data/bootstrap-run28/stage2/x86_64-unknown-linux-gnu/simple`
(132,930,184 bytes, commit `9c5e2dad378`). gdb exit status read directly into a
variable, not through a pipe.

```
rip 0x56bc65  hc_enc_hir_type+133    faulting insn: mov (%rcx),%rsi
rax 0x7251630  rbx 0x7250fd1  rcx 0xf198715900000000  rdx 0x7251631
rsi 0x1  rdi 0x7251601  rbp 0x72134a1  r12 0xf198715900000001  r14 0x7251610
```

### Classification: bad-pointer deref of a non-pointer that codegen untagged

**NOT the NULL-GOT class** (`rip` is valid, not 0) and **NOT the zeroed-payload
class**. Same third class as the AOT SEGV in
`selfhost_struct_method_hijacked_by_string_arm_2026-08-23.md`, but a **different
root cause** -- one fix does not resolve both.

Faulting sequence (`hc_enc_hir_type+70..+133`):

```
mov 0x8(%rax),%r12               ; r12 = node.span
call rt_alloc ($0x30 = 48)       ; sizeof(Span): 6 fields (span.spl:7-13)
mov %r12,%rcx
and $0xfffffffffffffff8,%rcx     ; untag as tagged pointer
and $0x7,%edx ; cmp $0x1 ; sete  ; tag == 1?
test %rcx,%rcx ; setne           ; base != 0?
=>  mov (%rcx),%rsi              ; SEGV, rcx = 0xf198715900000000 unmapped
```

The nil guard **passes**: tag == 1 and the masked base is nonzero. The address is
merely unmapped.

### Decisive fact

`0xf1987159` is `hash("Some")`, the runtime enum discriminant -- VERIFIED at
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:594`
(`if rt_enum_discriminant(raw_dest) == 0xf1987159:  # hash("Some")`).

So `r12` is not a pointer at all: it is an **inline `Some` enum word**
(`hash("Some") << 32 | 1`) sitting in a field declared as a plain struct.

### Source

`src/compiler/20.hir/generated/hir_codec.spl:4544` --
`fn hc_enc_hir_type(w: HirCodecWriter, node: HirType):`. The crash is in the
**parameter copy-in prologue** (value-semantics deep copy of `node.span: Span`),
before line 4545 executes.

Caller: `hir_codec.spl:4326`, `hc_enc_hir_type(w, o0)` inside `hc_enc_hir_symbol`
(`:4308`), where `o0` comes from `if val o0 = node.type_:` (`:4324`).
`HirType` is `kind, span: Span` (`src/compiler/20.hir/hir_types.spl:489-492`) --
16 bytes, matching the 2-qword copy into `%r14`.

### Not the same defect as the AOT SEGV (VERIFIED negative)

- No `rt_string_*` call is involved: the fault is an inline field dereference in
  generated copy code, not a call.
- `src/compiler/20.hir/` was grepped for declarations of
  trim/strip/lower/to_lower/to_upper/split/replace/rfind/find/contains/parse_f64/
  starts_with/ends_with -- **zero hits**. The string-arm hijack at
  `method_calls_literals.spl:~2382` cannot apply here.

### Remaining work (ASSUMED origin, VERIFIED symptom)

An `Optional<Span>` / `Some(...)` value reaches `HirType.span`, which is declared
non-optional; codegen then treats the enum word as a tagged `Span` pointer.

Next step: find the `HirType(... span: ...)` construction that passes an optional
un-unwrapped -- 149 `HirType(` sites in `src/compiler/20.hir/`; a suspicious
optional-typed span source is
`hir_lowering/_Items/module_declarations_bootstrap.spl:180`.

Secondary hardening (separate concern): the untag guard checks tag and nonzero
but never validates that the base is a real heap pointer -- the same weakness
noted for `rt_unwrap_or_trap` in `src/runtime/simple_core/core_values.spl:79-100`.

## 2026-08-23 -- ROOT CAUSE FOUND AND FIXED

### The construction site (VERIFIED)

Not a hand-written `HirType(...)` call: the **generated decoder**.
`src/compiler/20.hir/generated/hir_codec.spl` (pre-fix):

```
fn hc_dec_hir_type(r: FlatPoolReader) -> HirType:
    val f_kind = if r.next_i64() == 1: hc_dec_hir_type_kind(r) else: nil
    val f_span = if r.next_i64() == 1: hc_dec_span(r) else: nil
    HirType(kind: f_kind, span: f_span)
```

The if-**expression** unifies its two arms at `Span?`, so the taken arm is boxed
as an inline `Some` enum word (`hash("Some") << 32 | 1` = `0xf198715900000001`
-- exactly the observed `r12`). That word is stored into `HirType.span`, which is
declared **non-optional** (`src/compiler/20.hir/hir_types.spl:489-492`). The next
`hc_enc_hir_type(w, o0)` (`hir_codec.spl:4326`) then deep-copies `node.span` as a
tagged `Span` pointer in its parameter copy-in prologue -> SEGV.

This also explains cleanly why `SIMPLE_HIR_CACHE=0` bypassed D1: with the cache
off the **decoder never runs**, so the malformed `HirType` is never built.

The candidate flagged earlier, `module_declarations_bootstrap.spl:180`, is
**REFUTED** (VERIFIED): it passes `span: decl_span` where `decl_span = Span.empty()`
(line 46), a plain non-optional `Span`. Clean.

### Generator (VERIFIED)

`src/app/compiler_schema/codec_gen.spl`, `_emit_dec`, the `node`/`opaque` branch.
The comment immediately above it (the `prim_*` branch) records that **this exact
defect class was already hit and fixed for scalars** by inlining; the node/opaque
case was left unmitigated. 374 emitted sites carried the bug.

### Fix

Emit the **statement** form instead of the if-expression:

```
var <target>: <T>? = nil
if r.next_i64() == 1:
    <target> = <dec_fn>(r)
```

Plain assignment does not auto-box -- which is precisely why the sibling `opt`
branch in the same function must write `Some(...)` explicitly. **Wire format is
unchanged**; only the in-memory representation of the decoded local changes.

Fixed in the GENERATOR and regenerated (374 sites). Diff verified to contain
nothing else: 375 removed / 1123 added lines = 374 x (1 removed -> 3 added) plus
one relocated import line, with zero unexplained churn.

### Second defect found while regenerating (FIXED here)

Regeneration silently DROPPED a hand-added import from the generated file:

```
use compiler.hir.hir_types.{HirModule}  # explicit: a glob is not an import-origin for surface projection
```

Someone had edited the GENERATED file directly, so every regeneration wiped it.
The generator now emits it, and the spec pins that it survives.

### Third defect (reported, NOT fixed)

The type checker accepts a `Span?`-typed expression as the `span: Span` argument
of a struct literal. Had it rejected that, this SEGV could not have been written.
Site of the missing check is **ASSUMED/unlocated** -- deliberately no file:line is
quoted here rather than guess one.

### Reproduce test

`test/01_unit/compiler/hir/hir_codec_optional_node_decode_source_spec.spl`
(mirrored in `test/unit/`): **pre-fix 4 total / 0 passed / 4 failed** (374
if-expression occurrences), **post-fix 4/4 passed**. Verified by reverting both
source edits and re-running.

### Limit (honest)

Mechanism-level verification only. **stage2 remains miscompiled** -- it was built
before this fix -- so the SEGV persists in the existing binary until a bootstrap
redeploy. An end-to-end "hello world compiles AND runs under a self-hosted
binary" proof is NOT claimed. A behavioural encode/decode/re-encode round-trip
would only be a real regression pin on the NATIVE lane; under the tree-walk
interpreter it would likely pass either way, so it was not written as a false
assurance.

## 2026-08-23 — ROOT CAUSE FOUND AND FIXED

Status: **FIXED** (producer removed). Reproduced 1/1 on
`/mnt/data/worktrees/redeploy-1/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
(132,936,568 bytes, built from source byte-identical to `origin/main`
`dc86db785b4`), `native-build /tmp/hircodec_hw.spl` -> **rc=139**, dying at
step 2/6. gdb exit status read directly into a variable, never through a pipe.

### The value is GARBAGE, not nil

The earlier "nil `HirType`" hypothesis is **ruled out**. Every load in
`hc_enc_hir_type`'s copy-in prologue is paired with a `cmove` that substitutes
0 when the source is nil, so a nil `span` or a nil `HirType` is safe. `r12` is
a *non-nil, non-pointer* word that carries heap tag 1:

```
r12 0xf198715900000001   ; node.span
rcx 0xf198715900000000   ; r12 & ~7
=> mov (%rcx),%rsi       ; SIGSEGV  (rip 0x56bcd5, valid)
```

Classification: **untagged-non-pointer** (the third class), confirming and
refining the 2026-08-22 entry above.

### What `node` actually was

`0xf1987159_00000001` is exactly the inline enum word `hash("Some") << 32 | 1`
that `codec_gen.spl:468-479` already names. Dumping the object passed as
`node: HirType` showed it is **not a `HirType` at all**:

```
node        = {0x0000001800000007, 0xf198715900000001}   ; box header, Some word
node+0x10   = 0x72408f1 -> {0x7240891, 0x72408b1}        ; the REAL HirType
  its span  = {0, 0x23, 1, 1, <text*>, 0x23}             ; a valid 6-field Span
```

So `HirSymbol.type_` — declared `type_: HirType?`
(`src/compiler/20.hir/hir_types.spl:100-110`) — held a **heap `Some` box**
wrapping the real `HirType`, instead of the bare pointer the flat optional
representation requires. `hc_enc_hir_type` read the box header as `.kind` and
the `Some` word as `.span`, untagged it and dereferenced it.

### The producer

Breaking at `SymbolTable.define` showed the box already present in the `type_`
argument **at entry** — so the boxing happens in the caller, not in `define`
and not in codegen at the store boundary:

```
define name='main' type_=0x7240911 w0=0x1800000007
#1 module_declarations_bootstrap.HirLowering.declare_module_symbols
#2 module_build.HirLowering.lower_module
```

That call is `module_declarations_bootstrap.spl:137`, passing
`self.declared_callable_type(fn_decl, nil)`. `declared_callable_type`
(`module_callable_types.spl:97`) is declared `-> HirType?` and its **tail
expression was `Some(callable_type)`**. On the native lane an explicit
`Some(...)` allocates a heap Option box rather than lifting the bare value
into the optional slot — the "bare-lift" defect this repo already documents at
`module_declarations_bootstrap.spl:433` ("explicit `Some(...)` builds a heap
Option box on the stage4 native lane", 2026-07-23). Every other exit of that
same function returns a bare `nil`, and the sibling
`declared_surface_callable_type` four lines below already returns its value
bare — the `Some` tail was the odd one out.

Only ONE `hc_enc_hir_type` call ever executed before the crash: `main`, the
first symbol carrying a type. The defect is systematic, not data-dependent.

### Fix

Bare-lift, semantics-preserving, **no wire-format change**:

- `module_callable_types.spl` — `Some(callable_type)` -> `callable_type` (the
  primary producer).
- Six sibling sites passed a bare `HirType` wrapped in an explicit `Some(...)`
  into the same `type_: HirType?` parameter of `define`, poisoning the symbols
  for parameters, `self`, class fields, lambda parameters and contract
  bindings: `class_declaration_lowering.spl:15`,
  `declaration_lowering.spl:118,349,645`,
  `verification_contract_lowering.spl:19`, `expression_core.spl:602`.
- `declaration_lowering.spl:217` wrapped an *already* `HirType?` value in
  `Some(...)` — a double box; now a bare assignment.

### Still open (filed, not fixed here)

1. **The underlying codegen defect.** Explicit `Some(x)` in a `-> T?` position
   still produces a heap box on the native lane for USER code; this change only
   removes the compiler's own use of the pattern. Any Simple program written as
   `fn f() -> T?: Some(x)` remains exposed.
2. **The generated decoder** emits `f_type_ = Some(ov{k})` for `opt`-of-node
   fields (`codec_gen.spl:485-490`, 5 sites in `generated/hir_codec.spl`),
   which installs this same box shape on a cache HIT. Whether that re-poisons
   `HirType?` on the native lane must be checked by running a cached build
   twice; the generator, never the generated file, is the place to fix it.
3. `driver_aot_native_output._compile_frozen_module_capsule` SEGVs at step 5/6
   under `SIMPLE_HIR_CACHE=0`. Separate defect, separate lane.
4. `origin/main` `dc86db785b4` **cannot bootstrap from a fresh worktree**: it
   deleted `scripts/bootstrap/bootstrap-cache-policy.shs` while
   `bootstrap-from-scratch.sh:4383` still sources it (`exit 2`, "cannot open").

### Reproduce-spec honesty note (measured 2026-08-23)

`test/01_unit/compiler/hir/hir_symbol_type_bare_lift_encode_spec.spl` reports
`3 total, 3 passed, 0 failed` on the Rust seed **both** with the fix applied and
with the primary `Some(callable_type)` tail restored (verified by reverting that
one edit alone and re-running). The seed interpreter treats `Some(x)` and a bare
lifted `x` alike, so the spec does **not** discriminate pre-fix from post-fix on
that lane and must not be cited as if it did. It is a portable regression pin
for the lowering shape. The discriminating evidence for this bug is the
`native-build` rc on a self-hosted stage-2 compiler.
