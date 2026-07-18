# Self-host/native-build route hard-broken: `Map.new()` frontend const-eval → seed `.body`-on-String (no location)

- **Status:** ROOT-IDENTIFIED; canonical source fix landing separately (see
  "Fix ownership"). This doc records the self-host-route manifestation +
  bisect evidence + the diagnostic gap that made it expensive to find.
- **Discovered / bisected:** 2026-07-17, lane S53 (#138 self-host census)
- **Area:** seed compile-time interpreter (const-eval of live frontend
  sources) × pure-Simple frontend `Map.new()`/`Dict.new()` dict initializers
- **Severity:** Critical (native-build/self-host route 0/18 — EVERY
  `native-build`, even `fn main() -> i64: return 0`, fails before codegen)
- **Relation:** #185 (Map.new()/Dict.new() Dict-initializer regression),
  2nd bite. Guard test already exists: commit `d597355d9ed`
  `test(bug-185): guard against Map.new()/Dict.new() Dict-initializer regression`.

## Symptom

At origin tip `f6e7e2a18e5` (contains `71fe6f97be4 fix(bootstrap): harden
closure sets and frontend maps`), the pure self-host native-build route fails
for ANY entry:

```
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build \
    --entry <anything.spl> -o out --clean
...
error: semantic: undefined field: unknown property or method 'body' on String
```

Reproduced identically with `--entry src/app/cli/bootstrap_main.spl`, with a
trivial `print("hi")` entry, and with a bare `fn main() -> i64: return 0`
entry — the failure is **entry-independent** and occurs during the compile,
not at runtime. The oracle path (`env -u SIMPLE_BOOTSTRAP bin/simple run
<trivial>`) works fine — so it is **native-build-specific**.

`bin/simple` here is the Rust bootstrap seed (its own startup banner confirms:
"this Rust-built Simple binary is a bootstrap seed only"). The matrix uses the
same binary + invocation (`SIMPLE_BINARY` default `bin/simple`, matrix line
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 ... native-build --entry
... --clean`), so `scripts/check/native-smoke-matrix.shs` is 0/18 at this tip.

## Root cause

The error text is emitted by the **seed interpreter**, not by any
pure-Simple source:
`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:626`
(`format!("undefined field: unknown property or method '{field}' on String")`,
`Value::Str` receiver with an unknown field/no-arg-method).

During native-build the seed const-/global-evaluates the live frontend
sources it loads. `71fe6f97be4` re-introduced `Map.new()` / `Dict.new()` dict
initializers into three live frontend files. When the seed's compile-time
interpreter evaluates those initializers, a `.body` access lands on a value
that is a `String` at runtime, and the interpreter rejects it. Because the
failing access happens deep inside interpreted evaluation, the seed attaches
**no source span** — the error prints with no `-->` location, which is why it
reads as a bogus "first loud failure" in any self-host census probe.

Affected files (contained `Map.new()`/`Dict.new()` at this tip):
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (9),
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` (10),
`src/compiler/10.frontend/desugar/desugar_async.spl` (3).

## Bisect evidence (deterministic, same fixed seed binary)

- GOOD anchor: `57bfa1b5994` (`feat(mir): enum construction on native path
  (#141)`) — trivial native-build produces a binary, rc=0.
- GOOD: `37f566574d6`, `c3d4be926ed`.
- BAD: `f6e7e2a18e5` (tip).
- Culprit region: `c3d4be926ed..f6e7e2a18e5`; coordinator confirmed the
  reintroducing commit is `71fe6f97be4`.

Probe used per step (`bin/simple` symlinked to the Jul-11 deployed seed):
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build
--entry <trivial> -o out --clean`, grep for `body' on String`.

## Verified workaround (LOCAL, uncommitted — do NOT commit these 3 files)

```
sed -i 's/Map\.new()/{}/g; s/Dict\.new()/{}/g' \
  src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl \
  src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl \
  src/compiler/10.frontend/desugar/desugar_async.spl
```

With this applied, trivial native-build succeeds (binary produced, rc=0) — the
self-host route is restored. The canonical fix is a re-revert to `{}`
initializers landing on origin main separately (commit message
`fix(frontend): re-revert Map.new() dict initializers to {}`); re-fetch origin
and confirm it is present before running final gates. Do NOT commit the
workaround.

## Real next wall (behind this transient)

With the workaround applied, `native-build --entry
src/app/cli/bootstrap_main.spl` (full compiler self-host) parses/loads the
whole compiler+app+lib module graph, then goes quiet in
semantic/HIR/module-family analysis at rising RSS with no further output — the
known self-host PERF wall (consistent with
`deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`'s ~31.8 GiB RSS /
rc=124 on the full entry, and `bootstrap_parser_quadratic_source_refetch_2026-07-12.md`).
No loud correctness failure is reached before the perf wall.

## Diagnostic gap (secondary, seed-side — filed for visibility)

The seed's `undefined field ... on String` compile-time-eval error carries no
source span, forcing a full source bisect to localize a one-line frontend
regression. A span (const/global name + module) on compile-time-eval errors in
`interpreter/expr/calls.rs` would turn an hour-long bisect into a one-line
read. Seed-side (Rust); out of scope for pure-Simple lanes, recorded here so
the next self-host debugger does not re-derive it.

## Fix ownership

- Frontend `Map.new()`→`{}` re-revert: canonical fix landing on origin
  (separate lane). #185 guard test `d597355d9ed` already exists.
- This doc: census/bisect evidence + workaround + next-wall, for #138.
