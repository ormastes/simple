# Bootstrap fixed provider-inventory regression templates

These three source templates preserve the exact Task145 cold diagnostic bytes.
The provider goes at `src/compiler/probe_owner.spl`. Copy exactly one entry
template to `src/app/cli/bootstrap_main.spl` in a new isolated mini root:

- `positive_bootstrap_main.spl` expects output `145`, exit code `0`, and no MIR
  warnings for `BootstrapMethodProbe` or `read_sentinel`.
- `negative_bootstrap_main.spl` reaches a missing method and expects compile
  exit code `1`, an unresolved-method diagnostic naming `read_missing`, and no
  output artifact. An unrelated compiler failure is not a negative pass. Never
  execute an unexpected artifact.

The caller creates the six canonical Stage 3 source roots for the active K1 and
CUDA policies. For the pinned configuration used by the cold diagnostic, those
are `src/compositions/kernel_llvm_cranelift`, `src/compositions/cuda_static`,
`src/compiler`, `src/app`, `src/lib`, and `src/plugins`.

Use the self-hosted bootstrap producer selected by the Stage 3 owner; this
fixture does not authorize Rust fallback. The required selector is the exact
logical entry `src/app/cli/bootstrap_main.spl`, module
`app.cli.bootstrap_main`, `--entry-closure --mode dynload`, with
`SIMPLE_BOOTSTRAP=1` and `SIMPLE_BOOTSTRAP_STAGE3=1`. Require logs to prove
`bootstrap_fixed` was selected and that the compiler read the fixture copy at
the exact entry path. Retain the existing transcribed runner, helper hashes,
and session/resource guards; this README does not replace those owners.

The source-byte provenance is:

| Template | Cold diagnostic source | SHA-256 |
| --- | --- | --- |
| `probe_owner.spl` | Task145 `typed_local/src/compiler/probe_owner.spl` | `ec649975dd336869f9cb6df67314c46c8186951988cf714a3d295b6a83c1b739` |
| `positive_bootstrap_main.spl` | Task145 `typed_local/src/app/cli/bootstrap_main.spl` | `c3fcde337aa220210e0249223c7ba5845fd96dfa36447cace07dba3d214358d1` |
| `negative_bootstrap_main.spl` | Task145 `reachable_missing_method/src/app/cli/bootstrap_main.spl` | `1577caccff496a2c13bb4aba1efb5067a053f42922c721fa8660dcb1177e2aec` |

The cold positive baseline failed before producing an artifact with missing
class-provider metadata for `compiler.probe_owner.BootstrapMethodProbe`
(`probe_owner.spl:9:5`). Validation after the driver fix is pending separate
external receipts; this template set does not claim a pass. The negative case
was not run.

The existing compiler Stage 3 whole-build gate covers this driver path. These
files provide a bounded reproduction when a diagnostic owner stages them; they
are not auto-discovered BDD tests, a `simple run` target, or semantic cache
proof. No fixture copy or compiler execution is performed by merely tracking
these templates.
