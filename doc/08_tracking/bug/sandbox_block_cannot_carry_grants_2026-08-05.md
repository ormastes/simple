# `sandbox` block cannot carry `grant:` — grants require a `security gate`

**Status:** open
**Found:** 2026-08-05, while making WASI capability enforcement reachable from the CLI.

## Symptom

A standalone `sandbox` declaration parses and produces a working (deny-all)
capability table:

```
sandbox lonely:
    backend auto
    net deny all
```

Offering it an ungranted capability is correctly refused:

```
$ SIMPLE_EXECUTION_MODE=wasm SIMPLE_WASM_ENV=AWS_SECRET_ACCESS_KEY \
    AWS_SECRET_ACCESS_KEY=s simple run bare_sandbox.spl
error: wasm execution: WASI error: WASI capability denied environment variable 'AWS_SECRET_ACCESS_KEY'
```

But the same block cannot say what it *does* allow. Adding the `grant:` block
that the security-gate form accepts is a parse error:

```
sandbox reader:
    backend auto
    net deny all
    grant:
        Env["REPORT_ROOT"]
        ReadDir["/reports"]
```

```
error: compile failed: parse: Unexpected token: expected identifier, found Indent
```

## Consequence

The only way to grant a capability today is to wrap it in a `security gate`:

```
security gate SomeGate:
    from feature user
    to feature admin
    policy CanDoThing
    audit all
    sandbox my_sandbox
    grant:
        ReadDir["/reports"]
        Env["REPORT_ROOT"]
        AuditLog

sandbox my_sandbox:
    backend auto
    net deny all
```

So a module's realistic choices are "no policy at all" (unrestricted) or
"deny-all", unless its author also invents a from/to feature pair and a policy
name that may have nothing to do with why the module wants a sandbox. The repo
currently contains **zero** `security gate` declarations, which is consistent
with that ceremony being the blocker rather than a lack of need.

This is the direct reason no owned `.spl` module was given a useful capability
policy in this lane: the grammar makes a faithful three-line policy
(`grant: Env[...] ReadDir[...]`) unexpressible, and the available substitute is
either vacuous or requires unrelated declarations.

## Wanted

Let a `sandbox` block carry its own `grant:` list, so that a module can state
exactly the capabilities it needs without a `security gate` it does not
otherwise want. The rendering and runtime sides already handle this shape --
`WasiCapabilityTable::from_sandbox_lowering_sdn` recognises grants by indentation
under the sandbox name and does not care which surface form produced them, so
this is a parser/HIR-lowering gap only.

## Where

- Parser: the `sandbox` declaration form (rejects `grant:` as a child).
- Renderer: `src/compiler_rust/compiler/src/security.rs`,
  `sandbox_manifest_for_source` / `build_security_inventory_for_source`.
- Runtime (already correct, no change needed):
  `src/compiler_rust/wasm-runtime/src/wasi_env.rs`,
  `WasiCapabilityTable::from_sandbox_lowering_sdn`.
