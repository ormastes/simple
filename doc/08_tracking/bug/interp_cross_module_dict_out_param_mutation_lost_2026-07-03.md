# Bug: cross-module function calls lose in-place `Dict` mutation on an out-parameter

**Date:** 2026-07-03
**Severity:** P1 — silent no-op (function reports success, caller's collection
stays empty), discovered because it made `load_assets` unusable
**Status:** Workaround applied in `game2d/asset/{loader,table}.spl`; interpreter
fix pending

## Summary

When function `A`, defined in module `M1`, is called from module `M2` and
`A` mutates a `Dict<K, V>` parameter in place (e.g. `out_dict[key] = value`),
the mutation is **not observed by the caller in `M2`** after the call
returns — the caller's dict is unchanged, even though:

- the same mutation pattern works perfectly when `A` is defined in the
  *same file/module* as its caller;
- the callee's own view of the dict is correct (its `len()`/contents are
  right immediately after the mutation, inside `A`);
- the callee's return value (e.g. a computed `count`) is correct and
  observed correctly by the caller — only the aliased-parameter mutation is
  lost.

This is effectively "cross-module dict parameters are passed by value on
return, not by reference," even though same-module calls demonstrably use
reference semantics for the same `Dict<K, V>` type.

## Reproduction

`helper.spl`:
```spl
use std.common.sdn.value.{SdnValue}
use std.nogc_sync_mut.game2d.render.image.{Image}

pub fn walk_it(d: Dict<text, SdnValue>, out_images: Dict<text, Image>) -> i64:
    var count: i64 = 0
    for (name, entry_value) in d.entries():
        match entry_value:
            case Dict(inner):
                val r = Image.new("some/path.png")
                match r:
                    case Ok(img):
                        out_images[name] = img
                        count = count + 1
                    case Err(_):
                        pass_do_nothing
            case _:
                pass_do_nothing
    count
```

`main.spl`:
```spl
use helper.{walk_it}
...
var out_images: Dict<text, Image> = {}
val c = walk_it(d, out_images)
print "count={c} out_images.len()={out_images.len()}"
# prints: count=1 out_images.len()=0   <- WRONG, should be 1
```

The identical `walk_it` body, pasted directly into `main.spl` instead of
imported from `helper.spl`, correctly prints `out_images.len()=1`.

## Real-world instance found

`src/lib/nogc_sync_mut/game2d/asset/loader.spl`'s `_walk_images_dict` /
`_walk_sounds_dict`, called from `src/lib/nogc_sync_mut/game2d/asset/table.spl`'s
`load_assets` (a genuine cross-module call — `table.spl` imports these from
`loader.spl`). Both took an `out_images: Dict<text, Image>` /
`out_sounds: Dict<text, Sound>` parameter and mutated it in place. Every
`load_assets(...)` call returned `Ok(AssetTable)` with `images.len() == 0` and
`sounds.len() == 0` regardless of how many images/sounds the source SDN
declared — **`load_assets` never actually worked** for populating the table
(only atlas validation, which didn't depend on the out-param path for its
`Result`, partially worked; `_build_atlases` similarly lost its
`table.atlases` writes because `table.spl` itself was still passing `table`
across into a helper that populated a field via out-param-style mutation from
inside the same call chain rooted at a cross-module entry).

## Why it went undetected

No existing spec actually calls `load_assets(...)` and asserts on the
resulting `AssetTable`'s contents — `test/system/game2d_sdn_assets_spec.spl`
only asserts source-text markers (`fn load_assets(` present, fixture files
exist, diagnostic codes are wired), never the runtime behavior of a real
`load_assets(...)` call. This is a different flavor of the same
false-green pattern as the `atlas_builder.find_sprite` bug found the same
day (see `interp_early_return_bare_value_not_optional_wrapped_2026-07-03.md`):
missing runtime assertions, not incorrect ones.

## Fix applied (workaround)

Changed `_walk_images_dict`, `_walk_sounds_dict` (`loader.spl`) and
`_build_atlases` (`table.spl`) from "take a mutable out-parameter, mutate it,
return a count/nothing" to "build a fresh local dict, return
`Result<Dict<K,V>, AssetError>` (or a bare `Dict<K,V>`)". `load_assets` now
does `table.images = imgs` (etc.) with the returned value — a same-module
field write, which is unaffected by this bug. Confirmed working end-to-end
via the `spritesheet pack` CLI manifest round-tripping through
`load_assets`.

## Real fix needed

Interpreter: cross-module function calls must preserve reference semantics
for mutable collection parameters (`Dict`, and likely `[T]`/`List`) exactly
as same-module calls do. Compare the module-boundary argument-passing code
path against the same-module path — the same-module path evidently keeps a
shared reference; the cross-module path appears to clone/rebox the argument
at the call boundary (or drops the mutation when marshalling the return).

## Scope note

Only `src/lib/nogc_sync_mut/game2d/asset/{loader,table}.spl` were changed.
A parallel, less-developed copy exists at
`src/lib/nogc_async_mut/game2d/asset/loader.spl` (the default stdlib tier
per `doc/04_architecture/lib/runtime_family_tier_defaults.md`) but does not
share this out-parameter shape and was not touched — out of scope for this
change.
