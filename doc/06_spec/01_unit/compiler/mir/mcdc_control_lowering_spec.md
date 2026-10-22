# MC/DC control-decision MIR lowering

Executable source: `test/01_unit/compiler/mir/mcdc_control_lowering_spec.spl`.

Status: authored manual; this revision is UNRUN. Generated documentation and native SSpec execution require an admitted test host. No bootstrap seed interpreter result qualifies these scenarios.

The spec parses and lowers real source, then inspects serialized MIR. REQ-MCDC-STATIC-OFF-001 covers disabled/setup behavior; REQ-MCDC-SHORT-CIRCUIT-002 covers grouping and evaluation order.

| Scenario | Actual assertion |
| --- | --- |
| Static off | No legacy decision or condition probe instructions appear. The companion native token probe additionally rejects generated calls in off mode. |
| Static short circuit | One owner-qualified begin/end surrounds two owner-qualified condition calls; a mask call exists, and the RHS probe follows RHS evaluation. |
| Dynamic short circuit | Owner-qualified begin, condition and end occur in order; legacy probe instructions are absent. |
| Dynamic main | Owner-qualified configuration precedes the fail-closed controller load. |
| Explicit dormant option | Configuration remains present while controller loading is withheld. |
| Static/off main | Static configuration uses its declaration owner; off-mode setup is absent. |

The generated target names must follow the existing callable owner contract: static calls use `lib.nogc_sync_mut.mcdc.static_probe`, dynamic calls use `lib.nogc_sync_mut.mcdc.dynamic_probe`. Bare probe names cannot establish the required native link identity. `test/02_integration/compiler/mcdc_required_token_probe.spl` independently checks actual call operands and decision-token equality in off, static, dynamic, and excluded-source cases.
