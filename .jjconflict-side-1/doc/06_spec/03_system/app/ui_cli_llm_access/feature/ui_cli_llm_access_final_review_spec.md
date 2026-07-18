# Ui Cli Llm Access Final Review Specification

> _Fail closed unless the highest-capability review receipt matches the exact
> reviewed revision and canonical evidence manifest._

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## UI CLI access final review binding

### should accept only the reviewed revision and evidence

- Start UI access
- Review access history

<details>
<summary>Executable SSpec</summary>

```simple
step("Start UI access")
step("Review access history")
val (out, err, code) = process_run("sh", ["scripts/check/check-ui-cli-final-review.shs", "--check"])
if code != 0:
    fail("final UI CLI review gate failed: " + err)
expect(code).to_equal(0)
expect(out).to_contain("stale_receipt_rejected=pass")
expect(out).to_contain("common_contract=pass")
expect(out).to_contain("cli_routing=pass")
expect(out).to_contain("ui_wm_parity=pass")
expect(out).to_contain("shared_grammar_parity=pass")
expect(out).to_contain("schema=pass")
expect(out).to_contain("safety=pass")
expect(out).to_contain("action_history=pass")
expect(out).to_contain("live_transport=accepted")
expect(out).to_contain("performance=accepted")
expect(out).to_contain("generated_manual=pass")
expect(out).to_contain("direct_runtime_guards=pass")
expect(out).to_contain("spec_layout_guard=pass")
expect(out).to_contain("highest_capability_review=accepted")
```

</details>
</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Scenarios | 1 |
