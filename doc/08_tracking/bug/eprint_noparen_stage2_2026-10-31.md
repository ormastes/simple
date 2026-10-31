# eprint no-paren fails in pinned stage2 (2026-10-31)

Root bug: `eprint <expr>` (no parentheses, non-string-literal argument) is rejected by the
pinned stage2 compiler with `undefined variable eprint` during MIR lowering of stage3 modules
(app.cli.bootstrap_main, app.cli.parse_shard_main, app.cli.native_build_main, ...).

Root fix: PR #5567 (parser accepts `eprint <expr>`). The pinned stage2 predates it.

Workaround: rewrite each `eprint <expr>` whose argument does not start with a string literal
into `eprint(<expr>)`, tagged `# @workaround bug=eprint-noparen-stage2-20261031
reason=pinned-stage2-predates-#5567` on the line above. Behaviour is identical.

Removal condition: stage2 rebuilt from a tree containing #5567; then drop the parens and tags.

Workaround sites (tag line; the eprint( call is the next line):
- src/app/cli/bootstrap_main.spl (1)
- src/app/cli/check_entry.spl (3)
- src/app/cli/electron_entry.spl (2)
- src/app/cli/examples_check_entry.spl (2)
- src/app/cli/native_build_main.spl (4)
- src/app/cli/parse_shard_main.spl (1)
- src/app/cli/vscode_entry.spl (2)
- src/app/composite_test_entry.spl (1)
- src/app/test/font_evidence_runner.spl (3)
- src/app/verify/main.spl (1)
- src/app/verify/release_gate_cli.spl (10)
- src/app/verify/riscv_scalar_runtime_pipeline_v9_formal_bundle.spl (1)

Exact lines:
- src/app/composite_test_entry.spl:65
- src/app/test/font_evidence_runner.spl:175
- src/app/test/font_evidence_runner.spl:237
- src/app/test/font_evidence_runner.spl:286
- src/app/verify/main.spl:48
- src/app/verify/riscv_scalar_runtime_pipeline_v9_formal_bundle.spl:71
- src/app/verify/release_gate_cli.spl:26
- src/app/verify/release_gate_cli.spl:43
- src/app/verify/release_gate_cli.spl:50
- src/app/verify/release_gate_cli.spl:57
- src/app/verify/release_gate_cli.spl:80
- src/app/verify/release_gate_cli.spl:115
- src/app/verify/release_gate_cli.spl:133
- src/app/verify/release_gate_cli.spl:138
- src/app/verify/release_gate_cli.spl:145
- src/app/verify/release_gate_cli.spl:168
- src/app/cli/vscode_entry.spl:37
- src/app/cli/vscode_entry.spl:40
- src/app/cli/examples_check_entry.spl:69
- src/app/cli/examples_check_entry.spl:73
- src/app/cli/native_build_main.spl:1481
- src/app/cli/native_build_main.spl:1872
- src/app/cli/native_build_main.spl:1895
- src/app/cli/native_build_main.spl:2418
- src/app/cli/bootstrap_main.spl:427
- src/app/cli/check_entry.spl:208
- src/app/cli/check_entry.spl:212
- src/app/cli/check_entry.spl:219
- src/app/cli/parse_shard_main.spl:80
- src/app/cli/electron_entry.spl:33
- src/app/cli/electron_entry.spl:36
