# Setup-cost guard exit precedence

**SSpec AUTHORED_UNRUN.** This authored manual is not docgen output; no native Simple run or zero-stub result is claimed.

Executable `test/02_integration/app/test_runner/setup_budget_exit_precedence_spec.spl`, SHA-256 `07cebb7ca100675aa49a1038c829992a57f8c5f6dd51d20628b6c134fea9a61d`.

## Workflow

1. Execute the production setup-cost guard's selftest. Its real child fixtures cover fast success, missing verdict, deadline expiry, and a child that prints a verdict then exits 7. All four expectations must hold.
2. Execute the production session setup guard's selftest. Its five classifier fixtures additionally require nonzero exit to override an otherwise valid summary.

REQ-TEST-SETUP-EXIT-001: setup-cost admission requires a successful child process as well as existing verdict/deadline checks. Shell fixture execution is guard evidence only; it is not measured compiler startup, warm-cache latency, or a nested-daemon regression run. Production timeout budgets are unchanged.

After an admitted runner is available, execute the SSpec and regenerate with `simple spipe-docgen test/02_integration/app/test_runner/setup_budget_exit_precedence_spec.spl --output doc/06_spec --no-index`; inspect genuine zero-stub results.

<details><summary>Executable SSpec</summary>

```simple
"""
## Purpose and audience
Test-runner maintainers ensure setup-cost admission rejects a failed child even
when the child printed a green-looking summary before exiting.
## Operator workflow
Run with an admitted native test producer and --assert-ran --no-cache.
The shell owners also expose --selftest-only / --selftest for independent checks.
## Compatibility and limitations
SSpec AUTHORED_UNRUN: no admitted Simple runtime. Shell selftest evidence is
separate and does not measure Simple runner setup time or nested execution.
## Verification guidance and troubleshooting
A nonzero child exit must defeat a verdict string. Existing fast-success,
missing-verdict and over-budget fixtures retain their expected outcomes.
"""
# Lifecycle: doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md
# @manual_section: setup budget failure precedence
# @evidence-display: links
use std.spec.*
use app.io.process_ops.{process_run_bounded}

describe "Setup-cost guards reject failed child processes":
    it "should reject a child that emits a verdict and exits seven":
        # @req REQ-TEST-SETUP-EXIT-001
        # @capture(exec): real setup-cost guard selftest output and exit status
        step("Select the production setup-cost guard")
        val script = "scripts/check/check-test-setup-cost-budget.shs"
        step("Execute its process fixtures including verdict then exit seven")
        val result = process_run_bounded("sh", [script, "--selftest-only"], 120000, 65536)
        step("Require every fixture to satisfy the admission contract")
        expect(result.2).to_equal(0) # oracle: complete selftest succeeds, not measured compiler run
        expect(result.0).to_contain("4 fixture(s) checked, selftest only, no setup cost measured")

    it "should reject a failed session worker even with a complete summary":
        # @req REQ-TEST-SETUP-EXIT-001
        # @capture(exec): real session setup-budget classifier selftest output
        step("Select the production session setup guard")
        val script = "scripts/check/check-test-session-setup-budget.shs"
        step("Execute summary, deadline and nonzero-exit classifier fixtures")
        val result = process_run_bounded("sh", [script, "--selftest"], 120000, 65536)
        step("Require all five independent admission outcomes")
        expect(result.2).to_equal(0) # oracle: all classifier assertions complete
        expect(result.0).to_contain("PASS — 5 fixture(s) checked")
```
</details>
