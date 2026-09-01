# Layer Expert: Execution Metrics

The execution-metrics layer is a handle-free value/decision capsule between platform resource providers and build/test policy. It owns evidence quality, termination causes, resource quantities, cohort compatibility, explicit baseline lifecycle, budget decisions, robust anomaly decisions, and missing-span validation.

Platform collection is below this layer; test/build SDN adapters and CLI policy are above it. Never introduce `rt_*` imports here. Keep different memory quantities named separately and make unavailable evidence explicit.
