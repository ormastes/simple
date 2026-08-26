# JIT/HIR: `Some(x)` binding double-unwraps when the optional's payload is itself an enum

**Date:** 2026-08-24
**Severity:** HIGH (silent wrong value, no crash)
**Status:** FIXED in the seed source. **NOT deployed** — reaching `bin/simple` needs a seed rebuild+redeploy owned by the bootstrap lane.
**Fix:** `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`

## Defect

Binding `case Some(x)` has to cope with two representations of `T?`: a boxed
`Option` enum (literal `Some(v)`) and the "raw migration form" (the bare
payload, which natively compiled `T?`-returning functions produce). The lowering
discriminated them at runtime with

```text
if rt_enum_id(subj) >= 0: rt_enum_payload(subj)   # assume boxed Some
else:                     subj                    # raw payload
```

`>= 0` only asks *"is the subject some enum"*. That is ambiguous exactly when
the payload type is **itself an enum**: a raw `SdnValue?` holding
`SdnValue.Dict(d)` IS a real enum, so the test took the boxed branch and asked
`rt_enum_payload` for the SdnValue's OWN payload — unwrapping one level too far
and binding `d` instead of the `SdnValue`. Nothing crashes; the binding is
simply the wrong value, so every later read answers as if the data were absent.

The runtime already had the correct rule and the identical reasoning, in
`rt_unwrap_or_self` (`runtime/src/value/objects.rs:318`): *"Only the canonical
Option enum uses this compatibility helper. User enums may also be boxed
RuntimeEnum values; unwrapping those would turn `K? ?? fallback` into K's
payload and corrupt a later match."* The match lowering just never agreed with
it.

## Fix

One comparison: `rt_enum_id(subj) >= 0` → `rt_enum_id(subj) == OPTION_ENUM_ID`
(the reserved id `1`, mirrored from `runtime/src/value/objects.rs:259` with a
comment tying the two together). A user enum never has that id.

## Evidence

Minimal repro, self-contained apart from `SdnValue` (an enum), driving both
representations of the same optional:

```console
$ bin/simple run ax2.spl        # stock seed, JIT, 0 jit-fallbacks
RAW inline-arm kind=other       # <-- wrong: bound the payload, not the SdnValue
BOXED inline-arm kind=Dict
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run ax2.spl
RAW inline-arm kind=Dict        # interpreter is correct
BOXED inline-arm kind=Dict
$ /mnt/data/cargo-target-jitfix/release/simple run ax2.spl   # rebuilt seed
RAW inline-arm kind=Dict        # <-- fixed
BOXED inline-arm kind=Dict
```

`SIMPLE_JIT_STRICT=1` reproduces too, and `grep -c 'jit-fallback|falling back'`
is 0 on every run, so the JIT genuinely executed rather than silently deopting.

**Seed test suite** (same target dir, both builds from identical origin content
apart from this diff): `FAILED. 3866 passed; 8 failed` **before and after, with
a byte-identical failure list**. No regression, and no repair.

A correction worth recording, because it nearly became a false claim: an earlier
measurement appeared to show this fix repairing
`test_if_let_identifier_binding_copies_subject_value` and
`test_if_val_exists_check_binds_unwrapped_option_value` — two tests named for
exactly this defect class. That was an artifact of a stale working copy (98
lines behind origin), not of the change. Re-measured with the fix re-applied to
clean origin content, both tests are red before AND after; they are a separate
pre-existing failure (`control_flow_tests.rs:612`) that this fix does not
address. The A/B above is the only claim supported by evidence.

## Scope: what this does NOT explain

> **Superseded 2026-08-25 — see "Second defect" below.** The framing in this
> section ("parser-built vs hand-built") was wrong. The second defect is not
> parser-specific at all; it reproduces with a 24-line local enum and no
> imports. The "hand-built does not reproduce" observation was a probe artifact
> — that probe never called `.get` THROUGH the `Some` binding. Root cause is
> that enum-body methods were never registered in `method_return_types`, so the
> binding's static type degraded to `ANY` and the call was routed to the
> collection builtin `rt_index_get`.

A second, distinct defect with a similar surface is still OPEN. Reading through
a `case Some(x)` binding taken from a **parser-built** `SdnValue` tree still
answers as if keys were absent, and this fix does not change that:

- hand-built `SdnValue` + inline arm -> correct, before and after;
- `parse()`-built `SdnValue` + inline arm -> wrong, before and after;
- hoisting into a `var` first -> correct in both.

That is the defect worked around in `package_pins.spl` and
`completeness_seal/manifest.spl` (commit `6d35617d429`). Those hoists remain
necessary. Root cause unknown; the parser-built tree is not itself corrupt,
because the hoisted read finds every key.

## Deployment

The fix is in the Rust seed, so it changes nothing for anyone until a seed
rebuild is deployed to `bin/simple`. That is the bootstrap lane's redeploy, and
this record must not be read as "deployed". Verified only against a locally
built binary at `/mnt/data/cargo-target-jitfix/release/simple`
(60359136 bytes, 2026-08-24 21:38 UTC); the shared `bin/simple` was deliberately
NOT replaced, since other lanes' runs are bracketed against it.

## Second defect — root cause and fix (2026-08-25)

**Status:** ROOT-CAUSED and FIXED in the seed source (layer 1 of two);
NOT deployed; NOT committed by the investigating lane. A residual second
layer is narrowed and recorded below with its own minimal repro.

### What the "Scope" section above got wrong

Three claims in "Scope: what this does NOT explain" were disproved by
bisection, and the record must not be read through them any more:

1. **It is not parser-specific.** A `val a = mk()` where `mk() -> SdnValue`
   builds the tree by hand reproduces identically, and so does a **local enum
   in a 24-line file with no imports and no stdlib** (`LV` fixture below).
   "Hand-built does NOT reproduce" was true only because the earlier probe
   built the literal in the SAME function and never called `.get` through the
   binding.
2. **The `Some(x)` binding VALUE is correct.** Instrumented inline arm:
   `kind(av) = Dict(1)`. Neither `c30d214b84a` nor the "nested payload
   extracted twice" hypothesis is involved — `rt_enum_payload` is not on the
   path at all.
3. **The failing read is the NEXT method call, and it fails because the
   binding is typed `ANY`.** With `SIMPLE_DEBUG_METHOD_DISPATCH=1` the inline
   `av.get("waivers")` prints
   `[MIR-METHOD-DISPATCH] bare 'get' call: receiver ty = Any`, while the
   hoisted `hoisted.get(...)` is a qualified `SdnValue.get`. The hoist
   "worked" only because the `var` re-carried the static type.

### Root cause (layer 1, fixed): enum BODY methods never had a return type

`lookup_method_return_type` (`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:826`)
answers a method's type from `method_return_types["Type.method"]`. That
table is filled by the "Pre-register method return types" loop in
`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:1449`
for `Node::Function`, `Node::Class`, `Node::Struct`, `Node::Actor` and
`Node::Impl` — and **not for `Node::Enum`**. Methods declared inside an enum
body (`enum SdnValue: ... fn get(self, key) -> SdnValue?`,
`src/lib/common/sdn/value.spl:139`) therefore had NO entry, so on a receiver
that is KNOWN to be `SdnValue` (`recv_hir = Enum { name: "SdnValue", .. }`)
the lookup returned `TypeId(14) = Any`. The same gap exists on the import
side: `src/compiler_rust/compiler/src/hir/lower/import_loader.rs` registers
imported enum VARIANTS (`:392` direct, `:619` transitive) and registers
return types for `Node::Impl` methods (`:514`), but never for enum-body
methods.

Consequences, in order: `v.get(k) : ANY` → `case Some(x)` payload recovery
(`expr/control.rs:1444`, which needs a `Pointer{inner}` subject to keep `T`)
binds `x : ANY` → `x.get(k2)` lowers as a BARE `MethodCallStatic("get")` →
codegen's erased-receiver rule (`codegen/instr/closures_structs.rs:701`,
`is_bare_builtin_collection_method`) routes `get`/1 to `rt_index_get` BEFORE
any name resolution → `rt_index_get` on a user enum is a tag-dispatched miss
→ nil → `None`. Silent, exit 0.

Trace on the instrumented seed (new level-gated lines, default off):

```text
[HIR-METHOD-RET] .get recv_ty=TypeId(17) recv_hir=Some(Enum { name: "SdnValue", ..}) -> TypeId(14) (Some(Any))      # BASE
[HIR-PAT-BIND] Some(av) subject_ty=TypeId(14) (Some(Any)) binding_ty=TypeId(14) (Some(Any))                        # BASE
[HIR-PAT-BIND] Some(av) subject_ty=TypeId(19) (Some(Pointer { inner: TypeId(16) })) binding_ty=TypeId(16) (Enum LV) # FIXED
```

### Fix (diff)

`module_pass.rs` — add the missing `Node::Enum(e)` arm to the pre-register
loop, the same shape as the `Node::Struct`/`Node::Actor` arms next to it.
`import_loader.rs` — new helper `register_enum_method_return_types(enum_def)`
called from both imported-enum registration sites (direct and transitive).
Additive only: an unresolvable return type records `ANY`, which is what the
lookup returned before, so nothing can get worse.

```diff
--- a/src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs
+++ b/src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs
@@ Pre-register method return types (before lowering bodies)
+                Node::Enum(e) => {
+                    for method in &e.methods {
+                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
+                        let qualified = format!("{}.{}", e.name, method.name);
+                        self.method_return_types.insert(qualified, ret_ty);
+                    }
+                }
--- a/src/compiler_rust/compiler/src/hir/lower/import_loader.rs
+++ b/src/compiler_rust/compiler/src/hir/lower/import_loader.rs
@@ Node::Enum (direct import) and Node::Enum (transitive registration)
+                        self.register_enum_method_return_types(enum_def);
@@ impl Lowerer
+    fn register_enum_method_return_types(&mut self, enum_def: &simple_parser::ast::EnumDef) {
+        for method in &enum_def.methods {
+            let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
+            let qualified = format!("{}.{}", enum_def.name, method.name);
+            self.method_return_types.insert(qualified, ret_ty);
+        }
+    }
```

Instrumentation kept in the same change, level-gated on the pre-existing
`SIMPLE_DEBUG_METHOD_DISPATCH` switch (default off, per the log-retention
policy): `[HIR-METHOD-RET]` in `expr/mod.rs` (`lookup_method_return_type`
became a traced wrapper over `lookup_method_return_type_inner`) and
`[HIR-PAT-BIND]` at the variant identifier binding in `stmt_lowering.rs`.
They are what located this; the earlier `[MIR-METHOD-DISPATCH]` line alone
could only say "it is Any", not why.

### A/B on the exact repro from the task brief (verbatim)

Deployed `bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple` (seed,
predates `c30d214b84a`). BASE = local build of clean `origin/main`
`842e792fec4` (`/mnt/data/cargo-target-jitfix2/simple.BASE`, 60,631,040 B).
FIXED = same content + this diff (`/mnt/data/cargo-target-jitfix2-dbg/release/simple`,
60,609,240 B, 2026-08-25 00:56, and the redeploy of `/mnt/data/cargo-target-jitfix2/release/simple`).
`grep -c 'jit-fallback\|falling back'` = 0 on every JIT run, so no silent
deopt.

```console
$ bin/simple run repro.spl                                       # deployed seed, JIT
inline-arm: MISSING
hoisted-var: FOUND
param: MISSING
$ /mnt/data/cargo-target-jitfix/release/simple run repro.spl     # c30d214b84a-only build, JIT
inline-arm: MISSING
hoisted-var: FOUND
param: MISSING
$ /mnt/data/cargo-target-jitfix2/simple.BASE run repro.spl      # BASE (clean 842e792fec4), JIT
inline-arm: MISSING
hoisted-var: FOUND
param: MISSING
$ /mnt/data/cargo-target-jitfix2-dbg/release/simple run repro.spl   # FIXED, JIT
inline-arm: FOUND
hoisted-var: FOUND
param: MISSING                                                   # <-- residual, layer 2 below
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run repro.spl
inline-arm: FOUND
hoisted-var: FOUND
param: FOUND
```

Bisection fixtures, all MISSING on `simple.BASE` (measured on that binary,
not inferred) and FOUND on FIXED under JIT (interpreter FOUND throughout): `val a = mk()`, `mk().get(..)` direct,
`case Ok(root)` over `Result<SdnValue,text>`, `case Some(root)` over
`SdnValue?`, `val r = mkr(); match r`, and the no-import local-enum file:

```simple
enum LV:
    Leaf(text)
    Node(Dict<text, LV>)
    fn get(self, key: text) -> LV?:
        match self:
            case Node(d):
                if d.contains_key(key): Some(d[key]) else: None
            case _: None
fn mk() -> LV: ...            # Node({"assurance": Node({"waivers": Leaf("x")})})
fn main():
    val a = mk()
    match a.get("assurance"):
        case Some(av):
            match av.get("waivers"):
                case Some(_): print("FOUND")     # BASE: MISSING   FIXED: FOUND
                case None: print("MISSING")
        case None: print("none")
```

### Layer 2, OPEN: bare `get` on an ERASED receiver never reaches a user method

`param: MISSING` is a different defect and this fix cannot touch it: an
untyped parameter `fn via_param(a)` is legitimately `ANY`, and codegen's
deliberate erased-receiver rule (`closures_structs.rs:701`, comment block
above it) sends every bare `get`/1, `has`/1, `remove`/1, `keys`/0, ... to the
tag-dispatched builtin FIRST so that a bare name cannot bind to an unrelated
same-named user method by suffix (the `SymbolTable.get` / `ListIter.len`
segfault family). The builtin then nil-misses on a user enum. Minimal repro,
no parser, no match on the receiver:

```simple
use std.common.sdn.value.{SdnValue}
fn via_any(a, k: text) -> text:
    match a.get(k):
        case Some(v): "FOUND"
        case None: "MISSING"
fn main():
    var d: Dict<text, SdnValue> = {}
    d["s"] = SdnValue.String("x")
    print(via_any(SdnValue.Dict(d), "s"))   # JIT: MISSING   interpreter: FOUND
```

Same fixture: `a.as_dict()` (a non-builtin name) dispatches correctly on the
erased receiver, and `a.keys()` answers `-1` under JIT where the interpreter
reports `method keys not found on type enum` — both confirm the mechanism is
the builtin-name table, not the value. Fix site is the erased-receiver path
in codegen (Cranelift `codegen/instr/closures_structs.rs:701` and `:2248`,
`codegen/instr/calls.rs:3736`; LLVM `codegen/llvm/emitter.rs:361`,
`functions/calls.rs:2081`, `functions.rs:2642`) and needs a RUNTIME receiver
check (`rt_enum_id` → enum-owned candidate) before falling back to
`rt_index_get`. Deliberately not attempted here: multiple backends, a
segfault history on that exact path, and the typed fix above already repairs
the `package_pins.spl` / `completeness_seal/manifest.spl` class (their hoists
stop being necessary; they never had untyped params).

Sibling hazard noted, not fixed: the nested-struct-in-`Some` branch at
`stmt_lowering.rs:1616` still discriminates with `rt_enum_id(subj) >= 0`
rather than `== OPTION_ENUM_ID`. Unverified whether imported CLASS-body
methods share the layer-1 gap — `register_class` writes no
`method_return_types` either; worth one probe before assuming.

### Seed test suite

`CARGO_TARGET_DIR=/mnt/data/cargo-target-jitfix2 cargo test --release -p simple-compiler --lib`,
same box (load 20-25), exit status read directly:

- BEFORE (clean `842e792fec4`): `FAILED. 3888 passed; 6 failed; 2 ignored`.
  Provenance caveat, stated rather than hidden: the two env-gated
  `eprintln!` instrumentation edits landed while this baseline's test
  compile was still running, so the baseline test binary MAY contain them.
  They are inert without `SIMPLE_DEBUG_METHOD_DISPATCH`; the fix itself was
  applied only after that compile printed `Finished`.
- AFTER (this diff, `/mnt/data/cargo-target-jitfix2/release/simple`, 60,608,448 B, 2026-08-25 00:59):
  `FAILED. 3888 passed; 6 failed; 2 ignored` — exit 101 both runs, failure
  lists byte-identical (`diff` empty). after ⊆ before holds with equality:
  no regression, no repair. The 6 are pre-existing and unrelated (text/string
  receiver typing, vulkan extern parity, imported static-method symbols,
  simple-core runtime archive).

Failure list BEFORE (6):
```
hir::lower::tests::expression_tests::impl_text_self_chars_index_remains_a_string_receiver
interpreter::interpreter_extern::vulkan::tests::family_matches_runtime_rust_source
mir::lower::tests::branch_coverage::calls::text_rfind_does_not_resolve_to_trait_default
pipeline::lowering::tests::imported_static_methods_survive_lowering_with_context
pipeline::lowering::tests::native_object_defines_imported_static_method_symbol
pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive
```
Failure list AFTER: identical to the six above.

## Deployment

The fix is in the Rust seed, so it changes nothing for anyone until a seed
rebuild is deployed to `bin/simple`. That is the bootstrap lane's redeploy, and
this record must not be read as "deployed". Verified only against a locally
built binary at `/mnt/data/cargo-target-jitfix/release/simple`
(60359136 bytes, 2026-08-24 21:38 UTC); the shared `bin/simple` was deliberately
NOT replaced, since other lanes' runs are bracketed against it.
