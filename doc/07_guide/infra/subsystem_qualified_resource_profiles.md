# Native subsystem qualification resource profiles

The six-product runner defaults to 80 requested native build workers. The
canonical resource owner in `BootstrapProductProducer.pm` derives an explicit
profile from the requested qualification mode and worker count:

| Profile | Workers | Deadline | RSS |
| --- | --- | --- | --- |
| `qualified-80-v1` | Exactly 80 | Positive build and test deadlines | Enforced |
| `qualified-10-20-v1` | 10 through 20 | Positive build and test deadlines | Enforced |
| `diagnostic-v1` | 1 through 80 | Zero or positive | Monitored or enforced |

Qualified counts 21 through 79, and counts above 80, are rejected. The legacy
qualified range remains available to existing callers. This policy changes no
RSS ceiling, frontend shard allocation, source authority, producer admission,
binary registry requirement, or whole-suite pass criterion. Eighty requested
code-generation workers do not authorize eighty simultaneous frontend workers.
The existing frontend policy continues to require its bounded lane allocation.

New evidence records the profile in the build receipt, every command transcript,
product result, and matrix result. The product verifier checks the profile
against the actual requested resource tuple and the native `--threads` argument;
it retains the process-group RSS receipt checks. The matrix gate reuses the same
policy owner and requires matching product worker counts for qualified80.
Missing profile fields cannot qualify an 80-worker run. Legacy receipt fields
remain accepted only within previously supported profiles; this does not promise
replay across source generations or waive the complete regenerated-receipt check.

Diagnostic results remain diagnostic even when all observed cases pass. They
cannot satisfy the admitted producer, enforced resource, or formal matrix gates.
The focused policy and recording-child transport tests are infrastructure tests,
not native product qualification. A real Windows six-binary matrix with exact
enumeration, execution counts, positive deadlines, and enforced RSS remains
required before Windows RC1 admission.
