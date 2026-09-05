# `sandbox` block cannot carry `grant:` — grants require a `security gate`

**Status:** fixed 2026-08-05
**Found:** 2026-08-05, while making WASI capability enforcement reachable from the CLI.

## Fix

A standalone `sandbox` block now accepts its own `grant:` child, using the
same grammar `security gate`'s `grant:` block already accepted. This was a
parser/HIR-lowering-only change, confirming the "Where" section below:

- Parser: `SandboxPolicy` (`src/compiler_rust/parser/src/ast/aop.rs`) gained a
  `grants: Vec<String>` field; `parse_sandbox_policy`
  (`src/compiler_rust/parser/src/stmt_parsing/aop.rs`) now recognises a
  `grant:` key inside a `sandbox` block and parses it exactly like
  `parse_security_gate_after_keyword` already does for `security gate`.
- HIR: `HirSandboxPolicy`
  (`src/compiler_rust/compiler/src/hir/types/aop.rs`) carries the same
  `grants` field, populated in `module_pass.rs`'s `Node::SandboxPolicy` arm.
- Renderer: `src/compiler_rust/compiler/src/security.rs`'s `sandbox_grants`
  helper now merges grants from a targeting `security gate` **and** the
  sandbox's own `grants`, deduped, before `render_sandbox_manifest` /
  `render_sandbox_lowering` emit them. `sandbox_manifest_for_source` /
  `build_security_inventory_for_source` needed no changes beyond that.
- Runtime: `WasiCapabilityTable::from_sandbox_lowering_sdn`
  (`src/compiler_rust/wasm-runtime/src/wasi_env.rs`) needed **no change** —
  confirmed by running the exact repro through it: it already parses grants by
  indentation regardless of which surface form produced them.

Verified end to end through the real production seam
(`build_wasi_env`, not just the renderer) in
`src/compiler_rust/driver/tests/wasi_capability_enforcement.rs`
(`bare_sandbox_grant_*` and `bare_sandbox_without_grant_still_denies_everything`)
and in `src/compiler_rust/compiler/src/security.rs`'s
`sandbox_manifest_bridge_tests` (`bare_sandbox_grant_block_parses_and_renders_its_grants`,
`bare_sandbox_without_grant_still_renders_no_capabilities`). A sabotage check
(reverting the renderer's merge to ignore the sandbox's own `grants`) made the
new tests fail as expected, then was reverted.

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
