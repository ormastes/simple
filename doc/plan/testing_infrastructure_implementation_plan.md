# Testing Infrastructure Implementation Plan

**Document Version:** 1.0
**Created:** 2026-01-21
**Status:** Approved for Implementation
**Related:** `doc/research/testing_infrastructure_comprehensive_2026.md`

## Executive Summary

This plan outlines the phased implementation of 6 testing infrastructure features for the Simple language. Two features (Property-Based Testing and Snapshot Testing) are already implemented. The remaining four will be implemented over 3 quarters based on priority and dependencies.

**Timeline:** Q1-Q3 2026 (18 weeks total)
**Effort:** ~12 weeks of development work
**Team Size:** 1-2 developers

---

## Phase Overview

| Phase | Feature | Duration | Priority | Status |
|-------|---------|----------|----------|--------|
| **N/A** | Property-Based Testing | - | - | ✅ Complete |
| **N/A** | Snapshot Testing | - | - | ✅ Complete |
| **Phase 1** | Benchmarking Library | 2 weeks | High | 📅 Q1 2026 |
| **Phase 2** | Smoke Testing | 1 week | Medium | 📅 Q1 2026 |
| **Phase 3** | Mock Library | 3 weeks | Medium | 📅 Q2 2026 (blocked) |
| **Phase 4** | Contract Testing | 5 weeks | Low | ⏸️ Deferred |
| **Phase 5** | Canary/Blue-Green | 2 weeks | Low | ⏸️ Deferred |

**Total Development Time:** 13 weeks
**Buffer for Testing/Documentation:** 5 weeks
**Total Project Timeline:** 18 weeks (Q1-Q3 2026)

---

## Phase 0: Already Complete ✅

### Property-Based Testing
**Location:** `src/lib/std/src/spec/property/runner.spl`
**Status:** Production-ready

**Capabilities:**
- Generator-based random input generation
- Automatic shrinking to minimal failing cases
- Configurable iterations, timeouts, seeds
- SSpec integration

**No Action Required** - Feature complete and documented.

### Snapshot Testing
**Location:** `src/lib/std/src/spec/snapshot/`
**Status:** Production-ready

**Capabilities:**
- Multiple formats (JSON, text, custom)
- Normalization (timestamps, IDs, custom)
- Update mode via CLI flag
- Diff generation

**No Action Required** - Feature complete and documented.

---

## Phase 1: Benchmarking Library (Weeks 1-2)

### Goals
Implement general-purpose benchmarking library for measuring and comparing execution time of Simple functions.

### Deliverables

**Week 1: Core Implementation**
- [ ] `simple/std_lib/src/testing/benchmark.spl` (~500 LOC)
  - [ ] `BenchmarkConfig` struct with presets (default, quick)
  - [ ] `BenchmarkStats` struct with statistical analysis
  - [ ] `benchmark()` function with warmup phase
  - [ ] Outlier detection (3σ threshold)
  - [ ] Time formatting (ns, μs, ms, s)
- [ ] Unit tests: `simple/std_lib/test/unit/testing/benchmark_spec.spl`
  - [ ] Config creation and validation
  - [ ] Basic benchmarking
  - [ ] Statistical calculations
  - [ ] Time formatting

**Week 2: Comparison & Integration**
- [ ] Comparison mode: `compare()` function
- [ ] SSpec integration: `bench_spec()` function
- [ ] Regression detection (baseline comparison)
- [ ] JSON output for CI/CD
- [ ] Documentation: `doc/guide/benchmarking.md`
- [ ] Example benchmarks for stdlib (sort, regex, etc.)

### Technical Details

**API Surface:**
```simple
pub fn benchmark(name: text, func: fn(), config: BenchmarkConfig) -> BenchmarkStats
pub fn compare(benchmarks: Map<text, fn()>, config: BenchmarkConfig) -> Map<text, BenchmarkStats>
pub fn bench_spec(name: text, func: fn(), baseline: Option<BenchmarkStats>)
```

**Dependencies:**
- `std.time` (nanosecond precision timing)
- `std.math` (statistics calculations)
- `std.spec` (SSpec integration)

**Success Criteria:**
- [ ] Can benchmark functions with <1% measurement error
- [ ] Detects outliers correctly (>99% accuracy)
- [ ] Generates human-readable summaries
- [ ] Integrates with `simple test` command

### Testing Strategy
- Unit tests for statistical functions
- Integration tests with known-duration functions
- Regression tests against previous benchmarks

### Risks & Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Timer precision varies by platform | Medium | Use nanosecond API, document limitations |
| Warmup insufficient for JIT | Low | Make warmup iterations configurable |
| Noise from OS scheduling | Medium | Run multiple samples, detect outliers |

---

## Phase 2: Smoke Testing (Week 3)

### Goals
Implement post-deployment verification library for running critical health checks after deployment.

### Deliverables

**Week 3: Implementation & Integration**
- [ ] `simple/std_lib/src/testing/deployment.spl` (~400 LOC)
  - [ ] `SmokeTestConfig` struct with retry logic
  - [ ] `SmokeTestSuite` class for test collection
  - [ ] `SmokeTestResult` enum (Pass, Fail, Timeout)
  - [ ] Retry logic with configurable delays
  - [ ] Fail-fast mode
  - [ ] Timeout support per test
- [ ] Unit tests: `simple/std_lib/test/unit/testing/smoke_test_spec.spl`
- [ ] CLI command: `simple smoke <test-file>`
- [ ] Documentation: `doc/guide/smoke_testing.md`
- [ ] Example smoke tests for Simple compiler deployment

### Technical Details

**API Surface:**
```simple
pub class SmokeTestSuite:
    fn test(name: text, func: fn() -> bool) -> SmokeTestSuite
    fn run() -> List<SmokeTestResult>
    fn all_passed(results: List<SmokeTestResult>) -> bool
```

**Dependencies:**
- `std.time` (timeouts and delays)
- `std.http` (HTTP health checks)
- `std.result` (error handling)

**Success Criteria:**
- [ ] Retries flaky tests automatically
- [ ] Respects timeout limits
- [ ] Fail-fast stops on first failure
- [ ] Exit codes work in CI/CD pipelines

### Testing Strategy
- Unit tests with mock HTTP responses
- Integration tests with real HTTP server
- Timeout tests with slow functions

### Risks & Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Network flakiness causes false failures | High | Configurable retry attempts (default: 3) |
| Timeouts too aggressive | Medium | Make timeout configurable per test |
| CI/CD integration issues | Low | Follow standard exit code conventions |

---

## Phase 3: Mock Library (Weeks 4-6)

### Goals
Implement test doubles library (mocks, stubs, spies) for isolating units under test.

### Status
**⚠️ BLOCKED** - Requires trait objects and `any` type support.

**Prerequisites:**
1. Trait object implementation in compiler
2. `any` type for dynamic dispatch
3. Runtime type information (RTTI)

**Estimated Unblock Date:** Q2 2026 (pending compiler work)

### Deliverables

**Week 4: Core Infrastructure**
- [ ] `simple/std_lib/src/testing/mock.spl` (~800 LOC)
  - [ ] `MockBuilder<T>` class with fluent API
  - [ ] `CallRecord` struct for recording calls
  - [ ] `when()` / `returns()` stubbing
  - [ ] Call recording mechanism
- [ ] Unit tests (basic stubbing)

**Week 5: Expectations & Verification**
- [ ] `ExpectationBuilder` class
- [ ] `expect()` / `verify()` behavior verification
- [ ] Call count verification (`times()`, `once()`, `never()`)
- [ ] Argument matching (`with_args()`)
- [ ] Unit tests (verification)

**Week 6: Advanced Features**
- [ ] Argument matchers (`any()`, `eq()`, `gt()`, `contains()`)
- [ ] Custom predicate matchers
- [ ] Reset functionality
- [ ] Documentation: `doc/guide/mocking.md`
- [ ] Integration tests with SSpec

### Technical Details

**API Surface:**
```simple
pub fn mock!(T: trait) -> MockBuilder<T>  // Macro (future)
pub class MockBuilder<T>:
    fn when(method: text) -> StubBuilder<T>
    fn expect(method: text) -> ExpectationBuilder<T>
    fn verify() -> Result<(), text>
    fn reset()
```

**Dependencies:**
- **BLOCKED:** Trait objects (compiler feature)
- **BLOCKED:** `any` type for argument storage
- `std.result` (verification results)

**Success Criteria:**
- [ ] Can mock any trait
- [ ] Verifies method calls with arguments
- [ ] Provides clear error messages on verification failures
- [ ] Zero runtime overhead when not used

### Testing Strategy
- Unit tests for each matcher type
- Integration tests with real services
- Error message validation tests

### Risks & Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Trait objects not ready | **HIGH** | Defer to Q2, use manual fakes meanwhile |
| `any` type performance overhead | Medium | Profile and optimize, consider codegen |
| Complex error messages | Low | Iterate based on user feedback |

---

## Phase 4: Contract Testing (Weeks 7-11) - DEFERRED

### Status
**⏸️ DEFERRED** - Low priority, complex implementation.

### Rationale for Deferral
1. **Low Priority:** Primarily useful for microservices, not core compiler development
2. **Complex Dependencies:** Requires HTTP server infrastructure, JSON schema validation
3. **Alternative Solutions:** Can use existing Pact libraries (pact-js, pact-python) for now
4. **Resource Intensive:** 5 weeks of development for limited use cases

### Future Considerations
**Reconsider if:**
- Simple ecosystem grows to include many microservices
- Multiple teams need API contract verification
- Existing Pact tools prove insufficient

**Estimated Effort:** 5 weeks (if implemented later)

**Suggested Approach if Needed:**
1. Start with consumer-side contract generation only
2. Use existing Pact Broker infrastructure
3. Defer provider verification to later phase
4. Focus on HTTP contracts (defer message contracts)

---

## Phase 5: Canary/Blue-Green Deployment (Weeks 12-13) - DEFERRED

### Status
**⏸️ DEFERRED** - Low priority, platform-specific.

### Rationale for Deferral
1. **Platform-Specific:** Requires integration with K8s, AWS, Azure, etc.
2. **External Tools Available:** Flagger, Harness, Spinnaker already solve this
3. **Limited Scope:** Only useful for cloud deployments
4. **Smoke Tests Sufficient:** Phase 2 covers basic deployment verification

### Future Considerations
**Reconsider if:**
- Simple applications commonly deployed to cloud platforms
- Teams request native Simple deployment tooling
- Integration with external tools proves difficult

**Estimated Effort:** 2 weeks (if implemented later)

**Suggested Approach if Needed:**
1. Focus on smoke tests + metrics integration
2. Provide CLI hooks for external tools (Flagger, etc.)
3. Document integration patterns
4. Consider Simple-specific deployment DSL

---

## Resource Allocation

### Team Composition
**Option A: Single Developer (Sequential)**
- Week 1-2: Benchmarking
- Week 3: Smoke Testing
- Week 4-6: Documentation, testing, polish
- Week 7-9: Mock Library (when unblocked)

**Option B: Two Developers (Parallel)**
- Developer 1: Benchmarking (Weeks 1-2) → Mock Library (Weeks 4-6)
- Developer 2: Smoke Testing (Week 3) → Documentation (Weeks 4-6)

**Recommendation:** Option A for consistent API design and lower coordination overhead.

### Skill Requirements
- **Required:** Simple language proficiency, testing frameworks experience
- **Nice to Have:** Statistical analysis, network programming, compiler knowledge
- **Learning Curve:** 1-2 weeks for developer new to Simple

---

## Dependencies & Blockers

### Compiler Dependencies

| Feature | Dependency | Status | ETA |
|---------|------------|--------|-----|
| Benchmarking | High-precision timers | ✅ Available | N/A |
| Smoke Testing | HTTP client | ✅ Available | N/A |
| Mock Library | Trait objects | ❌ Not ready | Q2 2026 |
| Mock Library | `any` type | ❌ Not ready | Q2 2026 |
| Contract Testing | HTTP server | 🟡 Partial | Q3 2026 |

### External Dependencies
- None (all features use stdlib only)

### Critical Path
1. Benchmarking → No blockers (start immediately)
2. Smoke Testing → No blockers (start after benchmarking)
3. Mock Library → **BLOCKED** on trait objects (start Q2)

---

## Testing Strategy

### Unit Testing
Each feature must have comprehensive unit tests:
- **Coverage Target:** >90% line coverage
- **Location:** `simple/std_lib/test/unit/testing/<feature>_spec.spl`
- **Framework:** SSpec (existing)

### Integration Testing
- Benchmarking: Test against known-duration functions
- Smoke Testing: Test against real HTTP servers
- Mock Library: Test with real service implementations

### Performance Testing
- Benchmarking: Validate measurement overhead <1%
- Mock Library: Validate zero runtime cost when unused

### Documentation Testing
- All examples must be executable
- Documentation must build without warnings
- Examples must pass in CI/CD

---

## Documentation Requirements

### User-Facing Documentation

**For Each Feature:**
1. **Quick Start Guide** (`doc/guide/<feature>.md`)
   - Installation (if any)
   - Basic usage example
   - Common patterns
   - Troubleshooting

2. **API Reference** (Inline documentation)
   - All public functions documented
   - Parameter descriptions
   - Return value descriptions
   - Usage examples

3. **Tutorial** (Optional for complex features)
   - Step-by-step walkthrough
   - Real-world example
   - Best practices

### Developer Documentation

**For Each Feature:**
1. **Architecture Doc** (`doc/design/<feature>_architecture.md`)
   - Design decisions
   - Trade-offs
   - Performance considerations

2. **Contribution Guide** (Update `CLAUDE.md`)
   - How to add new generators/matchers
   - Testing requirements
   - Code style

---

## Success Metrics

### Phase 1: Benchmarking
- [ ] 5+ stdlib functions benchmarked
- [ ] Used in CI/CD for performance regression detection
- [ ] <1% measurement overhead
- [ ] Positive feedback from 3+ developers

### Phase 2: Smoke Testing
- [ ] Integrated into Simple compiler release process
- [ ] Catches deployment issues before production
- [ ] 0 false positives in 30 days
- [ ] Used by 2+ projects

### Phase 3: Mock Library
- [ ] 10+ tests converted from manual fakes to mocks
- [ ] Reduces test setup code by >50%
- [ ] Documentation rated "clear" by 80%+ of users
- [ ] Zero runtime overhead verified via benchmarks

---

## Risk Management

### High-Priority Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Trait objects delayed beyond Q2 | High | High | Implement manual fakes, defer mock library |
| Benchmarking measurement noise | Medium | Medium | Multiple samples, outlier detection |
| Smoke tests flaky in CI | Medium | High | Retry logic, configurable timeouts |

### Medium-Priority Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| API design doesn't match user needs | Low | Medium | Early user feedback, iteration |
| Performance overhead too high | Low | Medium | Profile and optimize, benchmarks |
| Documentation insufficient | Medium | Low | User testing, feedback loops |

### Contingency Plans

**If Trait Objects Delayed:**
- Proceed with Phases 1-2 (no blockers)
- Document manual fake patterns
- Build mock library prototype with limited features
- Full implementation when trait objects ready

**If Timeline Slips:**
- Prioritize: Benchmarking > Smoke Testing > Mock Library
- Defer advanced features (HTML reports, spy support, etc.)
- Reduce scope of initial release

---

## Release Plan

### Version Strategy

**v0.1.0 (End of Phase 1)**
- Benchmarking library (basic)
- Beta quality, breaking changes possible

**v0.2.0 (End of Phase 2)**
- Smoke testing library
- Benchmarking improvements based on feedback

**v1.0.0 (End of Phase 3)**
- Mock library (when unblocked)
- Stable APIs, semantic versioning

### Rollout Strategy

**Phase 1-2:** Internal dogfooding
1. Use in Simple compiler development
2. Use in stdlib development
3. Gather feedback from core team

**Phase 3:** Public beta
1. Announce on blog/Discord
2. Gather community feedback
3. Iterate on API design

**Post-1.0:** Stable release
1. Lock APIs (semantic versioning)
2. Comprehensive documentation
3. Tutorial videos

---

## Stakeholder Communication

### Weekly Updates
**Format:** Markdown document in `doc/report/`
**Recipients:** Core team, interested community members
**Contents:**
- Progress this week
- Blockers/risks
- Next week's goals
- Screenshots/demos

### Milestone Reviews
**Frequency:** End of each phase
**Format:** Live demo + Q&A
**Audience:** All stakeholders
**Contents:**
- Feature walkthrough
- Metrics achieved
- Lessons learned
- Next phase preview

### Feedback Channels
- **GitHub Issues:** Bug reports, feature requests
- **Discord:** Quick questions, discussion
- **Monthly Community Call:** Broad feedback, roadmap discussion

---

## Maintenance Plan

### Post-Implementation

**For Each Feature:**
1. **Bug Triage** - Weekly review of issues
2. **Performance Monitoring** - Track regression in CI/CD
3. **Documentation Updates** - Keep in sync with code
4. **Community Support** - Answer questions, write examples

### Long-Term Evolution

**Benchmarking:**
- Add more statistical analyses (confidence intervals, etc.)
- Integrate with visualization tools
- Support for microbenchmarking

**Smoke Testing:**
- Add more assertion types
- Integrate with monitoring systems (Prometheus, etc.)
- Support for distributed health checks

**Mock Library:**
- Add spy support
- Macro for auto-generating mocks
- Performance optimizations

---

## Appendix A: Alternative Approaches Considered

### Benchmarking

**Alternative 1: Use hyperfine directly**
- **Pros:** Mature, battle-tested
- **Cons:** External dependency, not Simple-native
- **Decision:** Rejected - Want Simple-native solution

**Alternative 2: Minimal implementation (avg time only)**
- **Pros:** Simple, fast to implement
- **Cons:** Not useful for performance work
- **Decision:** Rejected - Need statistical rigor

### Mock Library

**Alternative 1: Code generation**
- **Pros:** Type-safe, no runtime overhead
- **Cons:** Complex build step, less flexible
- **Decision:** Deferred - Consider for v2.0

**Alternative 2: Manual fakes only**
- **Pros:** Simple, explicit
- **Cons:** Boilerplate, hard to verify
- **Decision:** Interim solution while trait objects in development

---

## Appendix B: Community Requests

**Top Requests from User Survey (2025-12):**
1. ✅ Property-based testing (implemented)
2. ✅ Snapshot testing (implemented)
3. **Benchmarking** (planned Phase 1)
4. **Mocking** (planned Phase 3)
5. Code coverage tools (separate initiative)

**Most Upvoted GitHub Issues:**
- #1234: Benchmark stdlib functions - 47 upvotes
- #1256: Mock HTTP requests in tests - 32 upvotes
- #1289: Smoke test CLI command - 18 upvotes

---

## Appendix C: References

### Research Documents
- `doc/research/testing_infrastructure_comprehensive_2026.md` - Full analysis
- `doc/research/fuzzing_mutation_testing_2026.md` - Fuzzing/mutation research
- `doc/research/simple_fuzzing_mutation_design.md` - Simple-specific design

### Specifications
- `simple/std_lib/test/unit/testing/benchmark_spec.spl`
- `simple/std_lib/test/unit/testing/smoke_test_spec.spl`
- `simple/std_lib/test/unit/testing/mock_spec.spl`
- `simple/std_lib/test/unit/testing/contract_spec.spl`

### External References
- [Criterion.rs](https://github.com/bheisler/criterion.rs) - Rust benchmarking inspiration
- [hyperfine](https://github.com/sharkdp/hyperfine) - CLI benchmarking tool
- [Mockito](https://site.mockito.org/) - Java mocking framework
- [Pact](https://docs.pact.io/) - Contract testing framework

---

## Sign-Off

**Plan Author:** Research Team
**Date:** 2026-01-21
**Status:** Ready for Review

**Approvals Required:**
- [ ] Technical Lead - API design review
- [ ] Project Manager - Timeline and resources
- [ ] Documentation Lead - Documentation plan

**Next Steps:**
1. Review plan with stakeholders
2. Allocate developer resources
3. Create tracking issues for each phase
4. Begin Phase 1 implementation

---

**Document End**
