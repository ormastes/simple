# Old pure-Simple stage cannot parse GPU protocol split boolean

- **Status:** SOURCE FIXED / Stage2 direct check unsupported; Stage3 rebuild remains capped
- **Severity:** P1 bootstrap blocker
- **Owner:** `src/lib/common/gpu/simpleos_host_gpu_protocol.spl`

The frozen HYBRID/pure-Simple-bearing `build/redeploy_out/simple_stage2` reaches
current-source entry-closure discovery after two earlier compatibility repairs,
then stops at `simpleos_host_gpu_protocol.spl:180-183` with:

```text
Unexpected token: expected expression, found Indent
```

The condition is split after trailing `and`; the old deployed stage predates
the continuation grammar it is being asked to compile. Evidence is frozen in
`build/mini_builds/redeploy-current-stage3-20260811-cycle3.log`. The smallest
future repair is a semantics-preserving single-line condition, followed by one
cache-preserving failed-shard retry. The prior three-cycle rebuild lane
deliberately did not make that edit because cycle three was that lane's hard
verify/fix limit.

## Update 2026-08-11 — source compatibility repair

The guard is now expressed as the same three conjunctions on one physical
line. This changes no backend-admission behavior and avoids relying on the
newer trailing-operator continuation grammar. Existing focused protocol tests
already exercise Vulkan, Metal, DirectX, and unsupported preferred codes, so no
duplicate behavioral assertion was added. The capped Stage3 build was not
rerun. The HYBRID/pure-Simple-bearing Stage2 exposes no `check` subcommand
(`unknown command 'check'`), so a direct Stage2 source check was unavailable.
One existing focused protocol spec was run through `bin/simple`; the rewritten
backend-order example passed, including supported preferred-order and
unsupported-code cases. The file's overall result was 5/12 with seven
pre-existing protocol-version/receipt failures under the Rust bootstrap-seed
interpreter, so this is narrow branch evidence only and is not a whole-file or
pure-Simple verification claim.
