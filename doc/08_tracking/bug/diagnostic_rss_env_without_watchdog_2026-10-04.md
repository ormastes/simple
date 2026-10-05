# Diagnostic RSS environment without a watchdog

Status: reproduced transport-policy defect; active build remains diagnostic and unchanged.

The source-bound Cranelift Phase3 request `p3-next9d484-cranelift80-startup3` invokes the Hello-proven producer directly. It exports `SIMPLE_BOOTSTRAP_RSS_CAP_MODE=enforce` and `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=5242880`, but does not invoke the canonical RSS wrapper. The outer `windows-native-final-prep/unlimited-log-owner.py` contains log/Job cleanup bounds, not an RSS sampler or kill cap. The compiled native-build entry and worker do not consume these RSS environment names. Environment presence therefore does not establish enforcement.

Producer SHA: `0fce5d949d48b1a924c8131cc496ec191c8fce43033dbdc793386d819cc61e99`, producer source `20975fbf9eb33336b6f938b2e9c2b6d89fed70d3`; target source `9d484080c34c6e52ea001c5231c0f62bc0e383ea`. Actual root observation: HIR worker 36152 used 3,744,624,640 bytes and parent 62800 used 1,896,783,872 bytes, totaling 5,641,408,512 bytes, above the requested 5 GiB. These working-set samples are observations, not a measured peak or a diagnosis of compiler allocation growth.

The shared coordinator reserves a 5 GiB scheduling estimate with headroom. It does not enforce the process tree's working set. The frontend scheduling budget limits estimated concurrency, not actual RSS. Earlier wording that this particular transport enforced 5 GiB was incorrect. No RSS PASS can be inferred from its CFEC process/log receipt.

The earlier seed build `p2-next20975-cranelift-startup3/run.shs` uses the real integration point: export `SIMPLE_PROCESS_TREE_RSS_RECEIPT`, then invoke `scripts/bootstrap/run-process-group-timeout.shs`. That wrapper owns the process-tree sampler and RSS receipt. Preserve its real observation/cleanup contract for future enforce-mode runs. A monitored GoToEnd run must instead declare monitor-only explicitly and retain truthful resource samples.

A future launch contract must distinguish requested environment, admission estimate, and observed/enforced policy. Enforce-mode evidence requires the pinned watchdog entrypoint in actual argv and a terminal RSS receipt with the expected policy, limit, quiescence, and sampler status. Missing receipts are not PASS. Tests should reject direct producer launch mislabeled enforced, accept explicit monitor-only, and exercise the canonical wrapper with a bounded fake worker. Do not change or restart the active packet merely to amend its label.
