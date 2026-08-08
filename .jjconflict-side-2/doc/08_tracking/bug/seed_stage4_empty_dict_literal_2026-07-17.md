# Seed Stage4 `{}` empty-dict literal is NOT defective — the `{}` vs `Map.new()` land-war rationale is stale

**Date:** 2026-07-17
**Lane:** S57
**Severity:** N/A (no bug in `{}`); this doc SETTLES a recurring clobber war
**Status:** RESOLVED — `{}` verified clean on every seed path; respelling to
`Map.new()`/`Dict.new()` is actively harmful. Do not re-respell.

## TL;DR (read this before touching the three guarded frontend files)

The claim that motivated respelling `{}` back to `Map.new()`/`Dict.new()` in
the live frontend files — *"Explicit builtin construction avoids malformed
native `{}` values"* — **does not reproduce on any seed path** and is
**backwards**:

- **`{}` empty-dict literals are handled correctly on ALL four seed paths**
  (tree-walking interpreter, `SIMPLE_BOOTSTRAP=1`, `compile`→`.smf` bytecode
  VM, and real `--native --backend=cranelift` ELF), including the *exact*
  production shape `var functions: Dict<text, Function> = {}`, empty
  iteration, nested dicts, argument passthrough, and 100-key build-up.
- **`Dict.new()` / `Map.new()` FAILS the seed's compile / native path
  outright** with `semantic: Undefined("undefined identifier: Dict")`. So the
  respelling doesn't merely fail to help — it **breaks the seed compile/native
  path** that `{}` sails through cleanly.
- On top of that, `Map.new()`/`Dict.new()` is exactly what corrupts the
  **deployed** self-hosted binary (bug #185 phantom `__type__` entry via the
  deprecated `ClassName.new()` dispatch), which is the original reason the
  guard spec pins `{}`.

`{}` is strictly the SAFER spelling on the seed AND the deployed binary. The
guard in `test/01_unit/app/cli/bootstrap_main_source_spec.spl` ("never
re-introduce Map.new()/Dict.new() as a Dict initializer in the live frontend")
is correct — keep it green.

## Note to the session that keeps respelling `Map.new()` (commits f06e5829e1d, 71fe6f97be4)

You cited "malformed native `{}` values" when you inverted the guard and
respelled `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`,
`convert_nodes.spl`, and `desugar/desugar_async.spl`. I went looking for that
malformation with the from-scratch seed and could not produce it from `{}` on
any path. What you most likely saw was **one of two OTHER, real
malformations**, neither of which `Map.new()` fixes:

1. **The seed compile/native path cannot resolve `Dict`/`Map` as an
   identifier at all** — `Dict.new()`/`Map.new()` fails with
   `undefined identifier: Dict`. So respelling makes those files *fail to
   compile* on the seed's compile path instead of running.
2. **Functions that RETURN a `Dict` by value are miscompiled on native
   cranelift** (a genuinely malformed handle: `len()==-1`, garbage reads) —
   but this hits `Map.new()`-built and `{}`-built dicts *equally* (a
   non-empty returned dict is just as broken), so it is not a reason to prefer
   one spelling over the other. It is filed separately as
   `seed_native_cranelift_dict_return_abi_2026-07-17.md`. The three guarded
   files do not return bare `Dict`s (they build locally and pass the dict to
   `parser_module_new(...)`, which works), so that bug does not touch them.

Please stop respelling these three files. If you believe you have a *new*
`{}`-specific repro, add it to this doc with the exact command + output before
changing the files, and re-read the guard spec's comment block first.

## Reproduction (all commands from `src/compiler_rust/`, seed =
`./target/bootstrap/simple`, built from this same tree — the from-scratch seed)

Probe (`scratch_probe_struct.spl` — exact production shape, struct value type):

```simple
struct Function:
    name: text
    arity: i64

fn main() -> i64:
    var functions: Dict<text, Function> = {}
    print "F_LEN={functions.len()}"                 # empty: expect 0
    var empty_iter = 0
    for k in functions.keys():
        empty_iter = empty_iter + 1
    print "F_EMPTY_ITER={empty_iter}"               # expect 0 (no phantom entry)
    functions["add"] = Function(name: "add", arity: 2)
    print "F_LEN2={functions.len()}"                # expect 1
    print "F_HAS={functions.contains_key(\"add\")}" # expect true
    val fn0 = functions["add"]
    print "F_NAME={fn0.name}"                        # expect add
    print "F_ARITY={fn0.arity}"                      # expect 2
    0
```

Results — identical & correct on every seed path:

| path                                   | F_LEN | F_EMPTY_ITER | F_LEN2 | F_HAS | F_NAME | F_ARITY |
|----------------------------------------|-------|--------------|--------|-------|--------|---------|
| interpreter (`seed probe.spl`)         | 0     | 0            | 1      | true  | add    | 2       |
| `SIMPLE_BOOTSTRAP=1 seed probe.spl`    | 0     | 0            | 1      | true  | add    | 2       |
| `seed compile probe.spl -o p.smf`+run  | 0     | 0            | 1      | true  | add    | 2       |
| `seed compile --native --backend=cranelift` + run ELF | 0 | 0 | 1 | true | add | 2 |

Primitive value type (`Dict<text, i64> = {}`) and nested/100-key/passthrough
cases all likewise correct on every path (see `scratch_probe_bo.spl`,
`scratch_probe_edge.spl` — probes were exercised from the main repo working
tree and removed afterward).

The killer contrast (`scratch_probe_brace.spl`, which adds `Dict.new()` and
`Map.new()`):

```
$ seed compile scratch_probe_brace.spl -o /tmp/x.smf
error: compile failed: semantic: Undefined("undefined identifier: Dict")
```

vs the `{}`-only probe which compiles and runs cleanly.

## Root cause

There is **no `{}` root cause** — `{}` empty-dict lowering is correct in the
seed. The land-war was driven by a misattribution: a real native-cranelift
`Dict`-return miscompile (and/or the deployed binary's #185 phantom entry) was
blamed on the `{}` literal, and `Map.new()` was adopted as a "fix" even though
`Map.new()`/`Dict.new()` does not even compile on the seed's compile/native
path.

## Fix

None needed for `{}`. Action items:
1. Keep the three frontend files spelled with `{}`.
2. Keep the guard spec green
   (`test/01_unit/app/cli/bootstrap_main_source_spec.spl`, "never re-introduce
   Map.new()/Dict.new() as a Dict initializer in the live frontend (bug #185)").
3. The real adjacent native-codegen bug is filed separately (see Related).

## Related

- `seed_native_cranelift_dict_return_abi_2026-07-17.md` — the real
  Dict-return-by-value native miscompile found while investigating this.
- Bug #185 — deployed self-hosted binary `Map.new()`/`Dict.new()` phantom
  `__type__` entry (guard spec comment in
  `test/01_unit/app/cli/bootstrap_main_source_spec.spl`).
- `6b59a8c4bf7` — prior seed brace-form struct-init nil-fill fix (context: the
  seed has had brace-literal bugs before, but not this one).
