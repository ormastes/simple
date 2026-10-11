# Replay thread recorder and chaos scheduler specification

Status: **baseline 31 PASS / 1 FAIL; repaired boundary case 1 PASS / 0 FAIL**. Cycle one ran all 32 cases against the original owner: 31 passed, case 31 failed, 203 ms, exit 1. Its actual `next_random()` value was `-9223372036854775808`, violating the documented nonnegative result. The eight-draw reseed/history regression passed. No production-source failure of runnable membership is claimed from this receipt.

Evidence: `build/phase-one-storage-gui-diagnostic/replay_thread_chaos_spec/cycle-one.log`, sibling exit/resource receipts and `thread-chaos-cycle-one-inputs.sdn`. Peak RSS was 252192 KiB, enforced limit 5859375 KiB, quiescent=1. This is a coordinator-admitted bootstrap-seed diagnostic, not normal self-hosted/native qualification.

The repair maps only the minimum signed generator state to zero before negation. It leaves the LCG update, stored seed and every other output unchanged. Over the complete signed state domain, zero has two preimages (zero and minimum) just as every positive result has two (positive and negative); folding adds no imbalance to this output domain. The modulo-reduction algorithm is unchanged; no elimination of its bias is claimed. Tested production SHA-256: `a402e76302504a8560d5ea7d4a813914056ef92cf19579d205236983f6c5c945`.

Cycle two passed only original failed case 31: **1/1, 192 ms, exit 0**. The selected derivative `build/phase-one-storage-gui-diagnostic/replay-thread-chaos-boundary-cycle-two_spec.spl` retains its original assertions/imports, with an SDN source mapping alongside it. Evidence is in `replay-thread-chaos-boundary-cycle-two_spec/cycle-two.log` and sibling resource/exit receipts under that diagnostic directory. Peak RSS was 237784 KiB, enforced limit 5859375 KiB, quiescent=1. The coordinator verified all six files in `thread-chaos-cycle-two-inputs.sdn` before and after execution. The 31 baseline passing cases were not rerun. These results span two production snapshots; no complete repaired-source 32-case pass is claimed. Two diagnostic cycles were used; no further execution is needed for this repair.

This is an in-memory backend diagnostic. It does not qualify native OS-thread control, replay of a live process, concurrency fairness, whole-Phase1 admission, or measured branch coverage. The 80% `@cover` annotations are targets. Native/self-hosted checks and SPipe docgen remain unverified; this manually synchronized source is not a docgen receipt.

The canonical spec directly imports `src/lib/nogc_sync_mut/replay/process/thread_recorder.spl` and `src/lib/nogc_sync_mut/replay/process/chaos_scheduler.spl`, together with `std.spec`. Both production modules have no further imports. No process, file, FFI or OS-thread API is called by these scenarios.

## Boundary and reproducibility contract

Case 31 calls the production `next_random` and `pick_next` methods with seed `1843579416325869589`. Static modulo-2^64 arithmetic puts the documented LCG at the minimum signed state for this seed. The original source negated negative states before indexing; the repair handles the minimum before that negation. Cycle one established that this runtime returned the negative minimum from `next_random`; that observed result is the failure, without extrapolating it to every native backend. Assertions require the documented nonnegative random result, a returned runnable thread, and matching recorded history. The test neither implements an LCG nor uses copied output as an oracle.

Case 32 takes three real picks, reseeds to 999, and compares eight future picks against a fresh scheduler with that seed. It checks runnable membership, retains the exact three earlier decisions, and checks every appended history entry. Reseeding is documented as resetting the PRNG seed; it does not clear history or reset unrelated strategy state. Existing cases and their assertions remain intact; indexed assertions now have length guards because expectation failures do not abort a scenario.

## Canonical ownership

Requirement trace: `REQ-SSPEC-SYSTEM`, in-memory recorder/scheduler behavior. The legacy `test/system/replay_thread_chaos_spec.spl` was byte-identical to the original canonical spec (SHA-256 `a741af30084ac6f687ac8a7de27d57a1f9ac3701a9eb7d7d11fe3c95663e1949`) and is removed after preserving every scenario. No additional legacy requirement or tag was lost.

## Scenarios and visible steps

Each scenario has a visible `step(...)` describing its real operation. Cases 31–32 include separate generation/selection and reseed/history steps in the executable source below.

| Case | Scenario | Evidence |
|---|---|---|
| 1 | starts with zero threads | Baseline PASS; not rerun |
| 2 | starts with zero switches | Baseline PASS; not rerun |
| 3 | adds both parent and child to active set on first create | Baseline PASS; not rerun |
| 4 | does not duplicate parent on second create | Baseline PASS; not rerun |
| 5 | does not duplicate child if already active | Baseline PASS; not rerun |
| 6 | records a context switch | Baseline PASS; not rerun |
| 7 | records multiple switches | Baseline PASS; not rerun |
| 8 | removes tid from active threads | Baseline PASS; not rerun |
| 9 | handles exit of non-existent tid gracefully | Baseline PASS; not rerun |
| 10 | returns empty list with no switches | Baseline PASS; not rerun |
| 11 | returns to_tids in switch order | Baseline PASS; not rerun |
| 12 | Random to_i32 round-trip | Baseline PASS; not rerun |
| 13 | RoundRobin to_i32 round-trip | Baseline PASS; not rerun |
| 14 | StarveLast to_i32 round-trip | Baseline PASS; not rerun |
| 15 | PrioritizeNew to_i32 round-trip | Baseline PASS; not rerun |
| 16 | to_text returns human-readable name | Baseline PASS; not rerun |
| 17 | starts with zero schedule count | Baseline PASS; not rerun |
| 18 | replay_schedule is empty initially | Baseline PASS; not rerun |
| 19 | returns -1 for empty runnable list | Baseline PASS; not rerun |
| 20 | picks a valid tid from runnable list | Baseline PASS; not rerun |
| 21 | deterministic with same seed | Baseline PASS; not rerun |
| 22 | reseed changes future picks | Baseline PASS; not rerun |
| 23 | cycles through tids in order | Baseline PASS; not rerun |
| 24 | wraps around after exhausting list | Baseline PASS; not rerun |
| 25 | picks different tid from last pick | Baseline PASS; not rerun |
| 26 | falls back when only one tid available | Baseline PASS; not rerun |
| 27 | picks the highest tid (newest) | Baseline PASS; not rerun |
| 28 | consistently picks highest tid | Baseline PASS; not rerun |
| 29 | logs all picks for replay | Baseline PASS; not rerun |
| 30 | schedule_count matches log length | Baseline PASS; not rerun |
| 31 | keeps the signed-state boundary nonnegative and selects a runnable tid | Baseline FAIL; selected repair PASS |
| 32 | reseed reproduces an eight-pick sequence and preserves prior history | Baseline PASS; not rerun |

<details>
<summary>Exact executable SSpec source</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/replay/process/thread_recorder.spl 80%
# @cover src/lib/nogc_sync_mut/replay/process/chaos_scheduler.spl 80%
# Coverage percentages are admission targets, not measured coverage.
# @tag:system
# In-memory recorder/scheduler diagnostics; no native thread interleaving qualification.

use std.spec.{describe, it, expect, step}
use std.nogc_sync_mut.replay.process.thread_recorder.{ThreadRecorder, ThreadSwitchEvent, ThreadCreateEvent}
use std.nogc_sync_mut.replay.process.chaos_scheduler.{ChaosScheduler, ChaosStrategy}

# ============================================================================
# ThreadRecorder
# ============================================================================

describe "ThreadRecorder creation":
    it "starts with zero threads":
        step("starts with zero threads")
        val rec = ThreadRecorder.create()
        expect(rec.thread_count()).to_equal(0)

    it "starts with zero switches":
        step("starts with zero switches")
        val rec = ThreadRecorder.create()
        expect(rec.switch_count()).to_equal(0)


describe "ThreadRecorder on_thread_create":
    it "adds both parent and child to active set on first create":
        step("adds both parent and child to active set on first create")
        var rec = ThreadRecorder.create()
        rec.on_thread_create(1, 2, 1000)
        expect(rec.thread_count()).to_equal(2)

    it "does not duplicate parent on second create":
        step("does not duplicate parent on second create")
        var rec = ThreadRecorder.create()
        rec.on_thread_create(1, 2, 1000)
        rec.on_thread_create(1, 3, 2000)
        expect(rec.thread_count()).to_equal(3)

    it "does not duplicate child if already active":
        step("does not duplicate child if already active")
        var rec = ThreadRecorder.create()
        rec.on_thread_create(1, 2, 1000)
        rec.on_thread_create(1, 2, 2000)
        expect(rec.thread_count()).to_equal(2)

describe "ThreadRecorder on_thread_switch":
    it "records a context switch":
        step("records a context switch")
        var rec = ThreadRecorder.create()
        rec.on_thread_switch(1, 2, 0, 5000)
        expect(rec.switch_count()).to_equal(1)

    it "records multiple switches":
        step("records multiple switches")
        var rec = ThreadRecorder.create()
        rec.on_thread_switch(1, 2, 0, 5000)
        rec.on_thread_switch(2, 3, 0, 6000)
        rec.on_thread_switch(3, 1, 1, 7000)
        expect(rec.switch_count()).to_equal(3)

describe "ThreadRecorder on_thread_exit":
    it "removes tid from active threads":
        step("removes tid from active threads")
        var rec = ThreadRecorder.create()
        rec.on_thread_create(1, 2, 1000)
        expect(rec.thread_count()).to_equal(2)
        rec.on_thread_exit(2, 3000)
        expect(rec.thread_count()).to_equal(1)

    it "handles exit of non-existent tid gracefully":
        step("handles exit of non-existent tid gracefully")
        var rec = ThreadRecorder.create()
        rec.on_thread_exit(999, 5000)
        expect(rec.thread_count()).to_equal(0)

describe "ThreadRecorder get_schedule_order":
    it "returns empty list with no switches":
        step("returns empty list with no switches")
        val rec = ThreadRecorder.create()
        val order = rec.get_schedule_order()
        expect(order.len()).to_equal(0)

    it "returns to_tids in switch order":
        step("returns to_tids in switch order")
        var rec = ThreadRecorder.create()
        rec.on_thread_switch(1, 2, 0, 100)
        rec.on_thread_switch(2, 3, 0, 200)
        rec.on_thread_switch(3, 1, 0, 300)
        val order = rec.get_schedule_order()
        expect(order.len()).to_equal(3)
        if order.len() == 3:
            expect(order[0]).to_equal(2)
            expect(order[1]).to_equal(3)
            expect(order[2]).to_equal(1)

# ============================================================================
# ChaosStrategy
# ============================================================================

describe "ChaosStrategy enum":
    it "Random to_i32 round-trip":
        step("Random to_i32 round-trip")
        val s = ChaosStrategy::Random
        expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(0)

    it "RoundRobin to_i32 round-trip":
        step("RoundRobin to_i32 round-trip")
        val s = ChaosStrategy::RoundRobin
        expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(1)

    it "StarveLast to_i32 round-trip":
        step("StarveLast to_i32 round-trip")
        val s = ChaosStrategy::StarveLast
        expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(2)

    it "PrioritizeNew to_i32 round-trip":
        step("PrioritizeNew to_i32 round-trip")
        val s = ChaosStrategy::PrioritizeNew
        expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(3)

    it "to_text returns human-readable name":
        step("to_text returns human-readable name")
        expect(ChaosStrategy::Random.to_text()).to_equal("random")
        expect(ChaosStrategy::RoundRobin.to_text()).to_equal("round_robin")

# ============================================================================
# ChaosScheduler
# ============================================================================

describe "ChaosScheduler creation":
    it "starts with zero schedule count":
        step("starts with zero schedule count")
        val sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
        expect(sched.schedule_count()).to_equal(0)

    it "replay_schedule is empty initially":
        step("replay_schedule is empty initially")
        val sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
        expect(sched.replay_schedule().len()).to_equal(0)

describe "ChaosScheduler pick_next empty list":
    it "returns -1 for empty runnable list":
        step("returns -1 for empty runnable list")
        var sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
        val empty: [i64] = []
        val picked = sched.pick_next(empty)
        expect(picked).to_equal(-1)

describe "ChaosScheduler Random strategy":
    it "picks a valid tid from runnable list":
        step("picks a valid tid from runnable list")
        var sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
        val picked = sched.pick_next([10, 20, 30])
        var valid = false
        if picked == 10 or picked == 20 or picked == 30:
            valid = true
        expect(valid).to_equal(true)

    it "deterministic with same seed":
        step("deterministic with same seed")
        var s1 = ChaosScheduler.create(ChaosStrategy::Random, 123)
        var s2 = ChaosScheduler.create(ChaosStrategy::Random, 123)
        val tids: [i64] = [5, 10, 15, 20]
        val a = s1.pick_next(tids)
        val b = s2.pick_next(tids)
        expect(a).to_equal(b)

    it "reseed changes future picks":
        step("reseed changes future picks")
        var sched = ChaosScheduler.create(ChaosStrategy::Random, 1)
        sched.pick_next([1, 2, 3])
        sched.reseed(999)
        # After reseed, schedule_count is preserved
        expect(sched.schedule_count()).to_equal(1)

describe "ChaosScheduler RoundRobin strategy":
    it "cycles through tids in order":
        step("cycles through tids in order")
        var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
        val tids: [i64] = [10, 20, 30]
        val a = sched.pick_next(tids)
        val b = sched.pick_next(tids)
        val c = sched.pick_next(tids)
        expect(a).to_equal(10)
        expect(b).to_equal(20)
        expect(c).to_equal(30)

    it "wraps around after exhausting list":
        step("wraps around after exhausting list")
        var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
        val tids: [i64] = [10, 20]
        sched.pick_next(tids)
        sched.pick_next(tids)
        val third = sched.pick_next(tids)
        expect(third).to_equal(10)

describe "ChaosScheduler StarveLast strategy":
    it "picks different tid from last pick":
        step("picks different tid from last pick")
        var sched = ChaosScheduler.create(ChaosStrategy::StarveLast, 0)
        val tids: [i64] = [10, 20]
        val first = sched.pick_next(tids)
        val second = sched.pick_next(tids)
        # first and second must differ (two choices available)
        var differ = false
        if first != second:
            differ = true
        expect(differ).to_equal(true)

    it "falls back when only one tid available":
        step("falls back when only one tid available")
        var sched = ChaosScheduler.create(ChaosStrategy::StarveLast, 0)
        val tids: [i64] = [10]
        val picked = sched.pick_next(tids)
        expect(picked).to_equal(10)

describe "ChaosScheduler PrioritizeNew strategy":
    it "picks the highest tid (newest)":
        step("picks the highest tid (newest)")
        var sched = ChaosScheduler.create(ChaosStrategy::PrioritizeNew, 0)
        val picked = sched.pick_next([5, 100, 50])
        expect(picked).to_equal(100)

    it "consistently picks highest tid":
        step("consistently picks highest tid")
        var sched = ChaosScheduler.create(ChaosStrategy::PrioritizeNew, 0)
        val tids: [i64] = [3, 7, 2]
        val a = sched.pick_next(tids)
        val b = sched.pick_next(tids)
        expect(a).to_equal(7)
        expect(b).to_equal(7)

describe "ChaosScheduler replay_schedule":
    it "logs all picks for replay":
        step("logs all picks for replay")
        var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
        val tids: [i64] = [1, 2, 3]
        sched.pick_next(tids)
        sched.pick_next(tids)
        sched.pick_next(tids)
        val log = sched.replay_schedule()
        expect(log.len()).to_equal(3)
        if log.len() == 3:
            expect(log[0]).to_equal(1)
            expect(log[1]).to_equal(2)
            expect(log[2]).to_equal(3)

    it "schedule_count matches log length":
        step("schedule_count matches log length")
        var sched = ChaosScheduler.create(ChaosStrategy::Random, 77)
        sched.pick_next([10, 20])
        sched.pick_next([10, 20])
        expect(sched.schedule_count()).to_equal(2)
        expect(sched.replay_schedule().len()).to_equal(2)

describe "ChaosScheduler Random boundary and reseed contracts":
    it "keeps the signed-state boundary nonnegative and selects a runnable tid":
        step("Advance the real generator at the signed-state boundary")
        # Under wrapping i64 LCG arithmetic this seed reaches the minimum i64.
        # Runtime arithmetic is part of this diagnostic, not assumed qualification.
        val boundary_seed: i64 = 1843579416325869589
        var generator = ChaosScheduler.create(ChaosStrategy::Random, boundary_seed)
        val random_value = generator.next_random()
        expect(random_value).to_be_greater_than(-1)

        step("Select and record a real runnable thread using the same seed")
        var scheduler = ChaosScheduler.create(ChaosStrategy::Random, boundary_seed)
        val picked = scheduler.pick_next([10, 20, 30])
        expect(picked == 10 or picked == 20 or picked == 30).to_equal(true)
        expect(scheduler.schedule_count()).to_equal(1)
        val recorded = scheduler.replay_schedule()
        expect(recorded.len()).to_equal(1)
        if recorded.len() == 1:
            expect(recorded[0]).to_equal(picked)

    it "reseed reproduces an eight-pick sequence and preserves prior history":
        step("Record three scheduling decisions before reseeding")
        val runnable: [i64] = [11, 22, 33, 44, 55]
        var scheduler = ChaosScheduler.create(ChaosStrategy::Random, 1)
        val first = scheduler.pick_next(runnable)
        val second = scheduler.pick_next(runnable)
        val third = scheduler.pick_next(runnable)
        scheduler.reseed(999)
        expect(scheduler.seed).to_equal(999)
        expect(scheduler.schedule_count()).to_equal(3)

        step("Compare eight future picks with a fresh generator using the same seed")
        var reference = ChaosScheduler.create(ChaosStrategy::Random, 999)
        var actual: [i64] = []
        var expected: [i64] = []
        for draw in 0..8:
            val picked = scheduler.pick_next(runnable)
            val reference_pick = reference.pick_next(runnable)
            expect(picked == 11 or picked == 22 or picked == 33 or picked == 44 or picked == 55).to_equal(true)
            expect(picked).to_equal(reference_pick)
            actual.push(picked)
            expected.push(reference_pick)
        expect(actual.len()).to_equal(8)
        expect(actual).to_equal(expected)

        step("Inspect the retained history and all appended replay decisions")
        val recorded = scheduler.replay_schedule()
        expect(scheduler.schedule_count()).to_equal(11)
        expect(recorded.len()).to_equal(11)
        if recorded.len() == 11:
            expect(recorded[0]).to_equal(first)
            expect(recorded[1]).to_equal(second)
            expect(recorded[2]).to_equal(third)
            if actual.len() == 8:
                for draw in 0..8:
                    expect(recorded[draw + 3]).to_equal(actual[draw])
```

</details>
