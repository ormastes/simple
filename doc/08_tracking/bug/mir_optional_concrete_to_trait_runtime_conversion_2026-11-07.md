# `Concrete?` value returned into a `Trait?` slot is rejected

Status: OPEN (compiler, MIR native trait ABI). Not fixed; handed off to the
native-trait lane (recent commits `05b2dcfada0`, `0ea73925980`,
`4e1126681ab` in `native_trait_conversion.spl`).

## Symptom (bootstrap run 15, Stage 2 row `compiler_cli_build`)

`native optional trait conversion requires a matching declared payload` at
`src/os/compositor/hosted_backend.spl:357:20, 362:20, 378:16`:

```
fn select_hosted_backend(..) -> CompositorBackend?:
    val sdl = HostedSdl2Backend.try_create(w, h, title)   # HostedSdl2Backend?
    if sdl != nil:
        return sdl
    nil
```

## Root cause

`coerce_native_trait_object`
(`src/compiler/50.mir/_MirLowering/native_trait_conversion.spl` ~L35-67)
handles a `Trait?` slot for a `nil` literal, a value already typed `Trait?`,
and (since `05b2dcfada0`) a static `Some(<concrete>)`. A runtime value typed
`Concrete?` matches none of these: its declared source is
`Optional(Concrete)`, the owners differ, there is no `Some` argument, so it
fails. Still unhandled on origin/release/1.0.0 `fe52a1431e6`.

Valid Simple; the conversion needs a presence branch: nil stays nil;
present unwraps the payload, converts it to the two-word trait object with the
concrete impl, and re-wraps it as the `Trait?` handle.

## Reproduction

`build/repro5/main.spl` shape (trait `Backend`, class `Sdl` with
`static fn try_create(w) -> Sdl?`, `fn select(w) -> Backend?` returning the
checked local) fails on the run-15 Stage 2 binary with the exact message.

## Why not fixed here

The branch emits trait-ABI code that cannot be executed in this lane (Stage 2
is frozen; the seed does not run the pure-Simple MIR), and another lane is
actively changing this function. Source rewrite (`return Some(sdl)` via
`if val`) would route through the `Some(<concrete>)` path, which is not in the
frozen Stage 2 either, so it is also unverifiable here.
