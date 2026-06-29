# LLM Fine-Tune Guard Evidence

- status: `pass`
- strict_ready: `false`
- required_gates: `data_quality,retry6_training_eval,retry7_acceptance,retry6_spec,retry7_spec,tuned_model_acceptance`
- blocked_gates: `retry6_training_eval|retry7_acceptance|tuned_model_acceptance`
- primary_blocked_gate: `retry6_training_eval`
- blocker_reason: `guard_only_retry6_retry7_blocked`
- next_action: `complete retry6 training/eval gate before normal acceptance review`
- acceptance: `not_required`
- acceptance_reason: `default_guard_only`
- acceptance_pass_integrity_status: `not_required`
- acceptance_env: `build/llm_finetune_acceptance/evidence.env`
- surface_manifest: `build/llm_finetune_guard_evidence/fine_tune_guard_surface_manifest.tsv`
- surface_manifest_count: `11`
- surface_manifest_size: `1502`
- surface_manifest_sha256: `4649fd73873fc1e62cf1232402d6714aeac17493f3336c4c4fad0569af0c317f`
- fixed_format_data_quality: `pass` exit=`0` log=`build/llm_finetune_guard_evidence/fixed_format_data_quality.log`
- fixed_format_data_quality_log_size: `67`
- fixed_format_data_quality_log_sha256: `9c8fd3d817ac3378db09e63fd46142dde34246778b3aa06336f538b865f6ab42`
- retry6_direct_gate: exit=`pass` expected_status=`pass` expected_result=`pass` log=`build/llm_finetune_guard_evidence/retry6_direct_gate.log`
- retry6_direct_gate_log_size: `1366`
- retry6_direct_gate_log_sha256: `350b7de6f744fd7bea50157bf5fc2169f51e8adc5cd5e41f2cd2c86445d9093b`
- retry7_direct_gate: exit=`pass` expected_status=`pass` expected_result=`pass` log=`build/llm_finetune_guard_evidence/retry7_direct_gate.log`
- retry7_direct_gate_log_size: `2040`
- retry7_direct_gate_log_sha256: `05fd3bf2fc1c210b445e62a01cee639c6457221ebf3837bf0c69ac132d0cac18`
- retry6_spec: `pass` exit=`0` log=`build/llm_finetune_guard_evidence/retry6_spec.log`
- retry6_spec_log_size: `1456`
- retry6_spec_log_sha256: `d857f0ef8e9adfdb5b788bcd74b477b12e49a255691f01de11cd3eca853d9715`
- retry7_spec: `pass` exit=`0` log=`build/llm_finetune_guard_evidence/retry7_spec.log`
- retry7_spec_log_size: `1447`
- retry7_spec_log_sha256: `04e437fc8c90633d028ec696dc8338054e1d7f7f8875ed76285b343393eea17f`
- env: `build/llm_finetune_guard_evidence/evidence.env`

This evidence proves the local fine-tune process guards: fixed-format sample quality passes, retry6 remains blocked before licensed data/model/eval evidence, and retry7 remains blocked before retry6 target-eval plus normal-review evidence. It is not model training, target-eval, safety, deployment, or release-handoff proof. Run with `--strict-ready` when a tuned-model acceptance gate must pass.
