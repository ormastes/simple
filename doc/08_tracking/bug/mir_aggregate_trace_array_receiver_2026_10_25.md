# Aggregate trace array receiver metadata is lost after raw tuple extraction

Status: OPEN underlying MIR receiver-type propagation issue; source workaround cycle 2.

The earlier hoist in e3704dec moved `agg_operands.len()` out of interpolation and passed a diagnostic interpreter check. It did NOT fix native full-P3 lowering. The actual full03 log reports `unresolved method call 'len'`, `receiver_has_type=false receiver_type_kind=-1`, at `core_codegen.spl:1084:46`, the hoisted length call itself. Module-level fatal: `compiler.backend._MirToLlvm.core_codegen` at +1693499ms. Evidence is retained in `/Users/ormastes/wt/release-phase2-review/build/verify/provisional-p3-generic-len-object-20261025-03/logs/p3-build.log` (first warning line943468).

`agg_operands` is declared `[MirOperand]` but comes from generic raw tuple extraction. This workaround moves its length operation to a uniquely named helper with an actual concrete `[MirOperand]` parameter. The existing trace guard still performs one count and one print; the array and payload dispatch remain unchanged. No casts, generic erasure, runtime ABI changes, or diagnostic suppression are introduced.

The helper boundary regression checks empty, single, and paired operands. The real translator regression still constructs the aggregate with values17/29 at destination7 and verifies both emitted elements and destination bookkeeping. A native operator must also require the exact trace `MIRB-AGG fastpath-fired dest=7 operands=2`. Diagnostic interpreter success is not native qualification.

Remove the `@workaround` and helper only after the raw-tuple array local retains its receiver metadata and the original direct length call passes both this semantic regression and fixed native compilation. The live e3704 P3 source stays untouched; no P2 or runtime rebuild occurs.

Cycle 2 diagnostic validation: both SSpec cases executed and passed (2/2, no skipped/dropped cases), raw exit0; real trace `MIRB-AGG fastpath-fired dest=7 operands=2` observed. Existing-gen13 interpreter only, source/fixture/spec/seed hashes unchanged, enforced3GiB guard, peak966,832KiB, quiescent, zero observer errors. Evidence: `/Users/ormastes/wt/release-phase2-review/build/verify/llvm-aggregate-typed-count-interpreter-20261025-02/`. Native efficacy remains pending.
