# Real HIR codec generator baseline — 2026-11-14

The actual imported `app.compiler_schema.codec_gen.generate_codec_into` ran natively and generated **99 declarations / 428,476 bytes**, byte-identical to the checked-in HIR codec (`cmp` exit 0). No schema or generated file was hand-edited. This establishes the regeneration tool for the next named-aspect ownership packet; it does not implement that packet.

Input baseline: `release/1.0.0` at `ecb2d5059efcb2f601334e4adc59fc0b24a6c861`, with isolated diagnostic entry commit `97a8997a4d4` (local probe branch). Producer: admitted pure-Simple phase 2, SHA256 `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`; explicit `core-c` provider, one compiler thread, real source imports rather than extracted generator code.

| Attempt | Changed input / outcome |
|---|---|
| 1 | Source admission rejected four sparse-checkout directory aliases whose targets were omitted. Materializing the tracked Trace32 example targets fixed this checkout issue. |
| 2 | 60-second bound expired after real 71/71 MIR modules; no executable. |
| 3 | Same cache, 120-second deadline, 2 GiB RSS watchdog; exit 88 at 2,097,692 KiB during `process_ops` code generation. |
| 4 | Root-authorized 4 GiB RSS cap after an independent imported-IO build established that dependency needs more than 2 GiB. Compile exit 0, peak 2,764,564 KiB. Actual parse reuse: 71 FPC hits; native cache had zero hits before this build. |

Native generation then exited 0 under a 30-second / 2 GiB RSS watchdog, peak 548,372 KiB. The 4 GiB cap replaced an address-space cap; the repository process-tree RSS watchdog enforced the bound. No further cap escalation or unchanged retries were performed.

The diagnostic entry is reproducible with this body (supply private absolute input/output roots):

```simple
use app.compiler_schema.codec_gen.{generate_codec_into}

fn main() -> i64:
    val count = generate_codec_into("/tmp/simple-aspect-codec-baseline-20261114", "/tmp/aspect-codec-baseline-evidence-20261114/generated")
    if count <= 0:
        return 1
    print "generated codec declarations: {count}"
    0
```

Compile with the admitted producer's `native-build --source src --entry src/app/compiler_schema/codec_baseline_probe.spl --entry-closure --cache-dir <private-cache> --runtime-bundle core-c --threads 1 -o <private-output>`. The source is a real committed Git worktree. Watchdog receipts, compile/run logs, provenance, executable and generated output are retained in `/tmp/aspect-codec-baseline-evidence-20261114`; input worktree is `/tmp/simple-aspect-codec-baseline-20261114`.

Executable SHA256: `2b78217c925aa434aa1c5c4c0846ecdffccbbbac05f395f500ee24073749319c`. Generated codec SHA256: `de8562eb09e5bb2b6bb0d3eb7e8f71fd7775f6dbfdb0650aa90398ecb0b6497f`.
