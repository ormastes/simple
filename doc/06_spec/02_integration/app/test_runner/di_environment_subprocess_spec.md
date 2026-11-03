# DI flags across the test-runner subprocess boundary

AUTHORED_UNRUN. Authored manual, not generated; zero-stub qualification is unavailable.
Proof class: real subprocess contract, execution pending; this is not daemon-reuse evidence.

Spec SHA256 (LF bytes): `b6bc9fcfa63a53f15bf565b869f85ab968765283a841202ffacc0f2bb80ebbd3`.
No execution artifact exists. Fixtures are source artifacts, not run receipts.

Launch a tagged system fixture under contradictory caller flags and require the child to observe system=1, exemption=1, production DI lock=false. Launch an untagged fixture under an inherited exemption and require system=1, exemption=0, lock=true. Each child must exit0 and emit its distinct post-assertion marker. --assert-ran refuses an empty test run; a marker alone is insufficient. Caller process environment remains untouched.

Requires POSIX /usr/bin/env and separately admitted source-matched full CLI in SIMPLE_TEST_ENV_RUNNER. The specification does not establish admission from that variable or build a compiler. It uses --no-session-daemon, --no-db and --no-cache. Generic environmentidentity/v2 daemon tests remain separate existing evidence, not credited here.

<details><summary>Authored executable specification</summary>

```simple
"""
DI flags must reach actual test subprocesses. AUTHORED_UNRUN.
Requires POSIX /usr/bin/env and an admitted source-matched full CLI path in
SIMPLE_TEST_ENV_RUNNER. No seed fallback, bootstrap or native build is performed.
No parent environment is mutated; each fixture executes in a separate process.
This tests the direct child route, not a persistent daemon's v2 handoff.
"""
# @req REQ-TEST-ENV-DI-001
use std.spec.*
use std.env.variables.{env_get}
use app.io.mod.{process_run_timeout}

# @inline
fn run_di_environment_fixture(name: text, caller_system: text, caller_di: text) -> (text, text, i32):
    val binary = env_get("SIMPLE_TEST_ENV_RUNNER")
    expect(binary == "").to_equal(false)
    val fixture = "test/fixtures/test_runner/feature/di_environment_" + name + "_spec.spl"
    process_run_timeout("/usr/bin/env", ["SIMPLE_SYSTEM_TEST=" + caller_system,
        "SIMPLE_DI_TEST=" + caller_di, binary, "test", fixture,
        "--no-session-daemon", "--no-db", "--no-cache", "--assert-ran",
        "--mode=interpreter", "--timeout", "30"], 45000)

describe "DI runner flags reach the spawned production lock owner":
    it "should deliver the tagged system exemption despite opposite caller flags":
        # @req REQ-TEST-ENV-DI-001
        step("Launch a tagged system fixture with caller lock flags disabled")
        val result = run_di_environment_fixture("tagged", "0", "0")
        step("Require real child assertions on both flags and the DI lock")
        expect(result.2).to_equal(0)
        expect(result.0).to_contain("DI_CHILD_TAGGED_ASSERTIONS_REACHED")

    it "should remove an inherited exemption from an untagged system fixture":
        # @req REQ-TEST-ENV-DI-001
        step("Launch an untagged system fixture with an inherited caller exemption")
        val result = run_di_environment_fixture("untagged", "0", "1")
        step("Require real child assertions on both flags and the DI lock")
        expect(result.2).to_equal(0)
        expect(result.0).to_contain("DI_CHILD_UNTAGGED_ASSERTIONS_REACHED")
```
</details>
