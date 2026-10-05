# Phase1 bootstrap builder invalid conditional branch layout

Status: fixed, focused bootstrap diagnostics qualified; whole Phase1 remains collecting.

Whole inventory source e59027c353e9ed6ea8ddf572424da70e188fe511, bootstrap-only producer SHA0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7. Private repair source669d900b477af5cb15cad14a91410e958d739a9a. Initial failed artifacts preserved under /home/ormastes/simple-linux-rc1-20261005/phase1-whole-inventory-one-worker/interim-results.

worker.spl and grouped_native_run.spl put else on an indented block body value line. process_evidence.spl aligned a nested else-body if with its enclosing if. Isolated exact source-function chunks and minimal fixtures reproduced expected expression foundElse / expectedIndent foundIf. Proper block else and nested indentation controls executed successfully. This repair only aligns those existing branch expressions; values and ownership behavior stay the same. Valid compact conditionals remain in use.

Existing originally failing specs now pass under admitted seed and enforcing5859375KiB process-tree guard: memory_policy6/6, grouped_native_run10/10, grouped_native_worker8/8. Positive real examples24. No green whole/discovery/spec rerun. Source repair does not claim normal self-hosted CLI qualification. failure_dispatch passes former process-evidence parse boundary but is separately blocked by phase_admission mixed inline-if/block-elif/final-else Rust-seed parser defect; this valid concise grammar is being repaired independently, with its unchanged failing minimal fixture retained. No grammar workaround applied there.

Evidence: /home/ormastes/simple-linux-rc1-20261005/phase1-source-grammar-evidence; parser shape fixtures /home/ormastes/simple-linux-rc1-20261005/phase1-parser-shapes. Source/runtimes and failed receipts remain bound to original attempts. Provider input/output/cache tokens unavailable, provider cost unavailable, cohort average unavailable, ratio to cohort unavailable. No costs estimated.
