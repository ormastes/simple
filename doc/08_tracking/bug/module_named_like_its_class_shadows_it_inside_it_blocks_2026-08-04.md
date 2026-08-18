# A module whose basename equals its class shadows the class inside `it` blocks

- **ID:** `module_named_like_its_class_shadows_it_inside_it_blocks_2026-08-04`
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found:** 2026-08-04
- **Severity:** high (64 failing examples —
  `test/01_unit/compiler/mdsoc/transform_adapters_spec.spl` and its
  `test/unit/` mirror, 32 each)

## Symptom

`MirProgram` is a class declared in
`.../mir_to_backend/entity_view/MirProgram.spl` — module basename and class
name are the same string. Calling a static factory on it works at module scope
and inside `fn main`, but **not** inside a `describe`/`it` body:

```
use compiler.mdsoc.transform.feature.mir_to_backend.entity_view.MirProgram.{MirProgram}
... (the spec's other 7 entity_view imports)

fn main():
    val p = MirProgram.empty()
    print "ok"                                     # -> ok
```

```
use ...MirProgram.{MirProgram}
... (same 7 other imports)

describe "probe":
    it "static factory inside it-block":
        val p = MirProgram.empty()                 # -> FAILS
```

```
semantic: method `empty` not found on type `dict` (receiver value:
  {MirProgram: <constructor:MirProgram>,
   MirProgram__empty: <fn:MirProgram__empty>,
   MirProgram__has_extern_fns: <fn:MirProgram__has_extern_fns>,
   MirProgram__has_functions: <fn:MirProgram__has_functions>, ...})
```

The receiver is the **module namespace dict**, not the class: the class itself
is sitting inside it under the key `MirProgram`, and the static methods are
name-mangled beside it as `MirProgram__empty` etc. So inside the `it` closure
the bare name `MirProgram` resolved to the module, while at module scope the
identical expression resolved to the class.

## Root cause

Two facts combine.

1. Importing a single symbol registers the **whole** module under its own
   last-path-segment name — the behaviour already recorded in
   `.claude/memory/reference_importing_one_symbol_registers_a_whole_module.md`.
   For `entity_view/MirProgram.spl` that segment is `MirProgram`, which is
   exactly the name the `use ....{MirProgram}` clause binds to the class. Two
   bindings, one name.

2. Which of the two wins depends on the scope doing the lookup. Module scope
   and `fn` bodies pick the imported class; the environment a `describe`/`it`
   closure body is evaluated in picks the module dict.

Control, same file, same 8 imports, same `it` block, but a module whose
basename differs from the class it exports (`hir_to_mir/entity_view/HirView.spl`
exporting `CfgContext`):

```
    it "control: module basename differs from class name":
        val c = CfgContext.empty()
```
```
semantic: unknown static method empty on class CfgContext
```

`CfgContext` resolved to **the class** (the error is only that my probe named a
method that does not exist). Name collision is therefore the trigger, and the
`it`-block scope is the discriminator. Every failing adapter in
`transform_adapters_spec.spl` — `MirProgram`, `MirDebugInfo`, `TokenStreamView`,
`MirOptView`, `ObjectFileView`, `LoadedModuleView` — is a
module-basename-equals-class-name case; the two that pass (`TypedAstContext`
from `TypedAstView.spl`, `CfgContext` from `HirView.spl`) are not.

The `describe`/`it` intrinsics are Rust-side (`bdd.rs`) and so is the name
resolution that disagrees with module scope; `grep -rn "ExistsCheck\|bdd"` over
`src/compiler/` shows the pure-Simple compiler has no counterpart, and the
deployed `bin/simple` is the Rust seed (it prints the seed banner), so the
divergence is entirely inside `src/compiler_rust/`.

## Why not fixed now

The honest fix is to stop registering the whole module under a name that can
collide with a symbol the same `use` clause binds — but that registration is
load-bearing for other import forms, and changing it is the same change already
flagged as a security concern in the memory note above. Making the `it`-closure
environment agree with module scope is the narrower fix, and it is also Rust-seed
only; landing it requires rebuilding the seed and replacing the live
`bin/simple` that other concurrent sessions in this working copy are running
tests against.

The alternative that *is* pure-`.spl` — renaming the six MDSOC `entity_view`
module files so no basename equals its exported class — is a cross-tree rename
of a public module path and needs an owner for the MDSOC layer, not a test-fix
session.

## Content re-verification 2026-08-17 (m4_compiler_spl lane) — STILL OPEN

`grep -n "shadow" src/compiler/99.loader/module_loader.spl` returns **zero
hits**: no shadowing-precedence handling of any kind has been added to the
module loader since this doc was filed. The reported binding order (module wins
over the same-named class inside an sspec `it` block) is therefore unchanged in
current source. Classified by CONTENT, not by commit ancestry — see the
2026-08-17 CORRECTIONS: SHA reachability proves nothing in this repo.

Not reproduced by execution in this pass (no `Results:` line obtained), so this
is an OPEN-by-content verdict, not a re-measured RED.

## Execution re-verification 2026-08-17 — STILL RED (measured, minimal repro)

Binary identity:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59537240 2026-08-17 12:58:51.339525019 +0000
```

Minimal repro — a 6-line spec with a **single** import (the original doc used the
spec's 8; one is sufficient, which sharpens the root cause: the collision needs
only the one `use` clause whose last path segment equals the class it binds):

```simple
use compiler.mdsoc.transform.feature.mir_to_backend.entity_view.MirProgram.{MirProgram}

describe "probe":
    it "static factory inside it-block":
        val p = MirProgram.empty()
        expect p != nil
```

```
$ bin/simple test <repro>.spl --no-session-daemon
  ✗ static factory inside it-block
    semantic: method `empty` not found on type `dict` (receiver value:
      {MirProgram: <constructor:MirProgram>, MirProgram__empty: <fn:MirProgram__empty>,
       MirProgram__has_extern_fns: <fn:MirProgram__has_extern_fns>,
       MirProgram__has_functions: <fn:MirProgram__has_functions>)
SPEC FILE VERDICT: ... declared>=1 executed=1 passed=0 failed=1 dropped=0
Results: 1 total, 0 passed, 1 failed
```

Identical receiver-is-the-module-dict signature as originally filed. Not fixed in
this pass for the reason already given above: the `describe`/`it` closure
environment and its name resolution are Rust-seed-only (`bdd.rs`), so there is no
`.spl` edit that changes this result; a fix needs a seed rebuild and replacement
of the live `bin/simple`. OPEN with fresh RED evidence.

## Re-run 2026-08-17 on the NEWLY REDEPLOYED Rust seed — STILL RED

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

Same 6-line minimal repro as above:

```
$ bin/simple test <scratch>/modshadow_spec.spl --no-session-daemon
    semantic: method `empty` not found on type `dict` (receiver value:
      {MirProgram: <constructor:MirProgram>, MirProgram__empty: <fn:MirProgram__empty>,
       MirProgram__has_extern_fns: <fn:MirProgram__has_extern_fns>,
       MirProgram__has_functions: <fn:MirProgram__has_functions>)
SPEC FILE VERDICT: <scratch>/modshadow_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0
Results: 1 total, 0 passed, 1 failed
EXIT=1
```

**Verdict: STILL-OPEN.** The seed redeploy changed nothing here — byte-identical
receiver-is-the-module-dict signature. The blocker is unchanged: the fix is in
seed `bdd.rs` name resolution, not in any `.spl`.
