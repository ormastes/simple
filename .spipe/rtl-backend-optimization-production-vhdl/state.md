# RTL Backend Optimization Production VHDL

## Task Type
feature

## Refined Goal
Build a production-oriented RTL backend optimization path that introduces an explicit HWIR layer, target-aware VHDL hardening, toolchain verification lanes, and QoR/debug evidence for hardware-generated VHDL.

## Acceptance Criteria
1. HWIR foundation exists with typed module, port, signal, register, memory, FSM, pipeline, clock/reset, resource binding, source-map, and cost-model records.
2. Hardware-tagged MIR can be represented as HWIR without changing the existing direct VHDL emission fallback.
3. HWIR legality diagnostics expose stable `HWIR-E-*` codes for unsupported hardware constructs.
4. Existing VHDL backend behavior remains unchanged until the HWIR bridge is explicitly selected.
5. Toolchain validation plans or lanes cover GHDL analysis at minimum and preserve existing VHDL tests.
6. QoR and debuggability follow-on work has concrete artifacts or task boundaries before completion is claimed.

## Phase
implementation

## Source Plan
`doc/03_plan/agent_tasks/rtl_backend_optimization_production_vhdl_agent_plan.md`
