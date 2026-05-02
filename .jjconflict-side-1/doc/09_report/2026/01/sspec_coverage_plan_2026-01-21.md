# SSpec System Test Coverage Improvement Plan

**Date:** 2026-01-21
**Current Rust Coverage:** 58.61%
**Target:** Improve to 75-80% through system-level SSpec tests

## Executive Summary

SSpec tests ARE system tests - they execute actual Simple code through the full compilation pipeline (parse → HIR → MIR → codegen/interpret → execute). The current plan focuses on **end-to-end integration scenarios** that exercise multiple components together.

**Existing System Coverage:**
- ✅ Language features: 87 tests in `simple/test/system/features/`
- ✅ Compiler/Interpreter: 13 tests
- ✅ Macros, mixins, SDN: 44 tests in `simple/std_lib/test/system/`
- ❌ **Missing:** Collections integration, networking workflows, process pipelines, file I/O workflows

## Test Level Strategy

| Test Type | Location | Purpose | Status |
|-----------|----------|---------|--------|
| **Unit** | `simple/std_lib/test/unit/` | Individual function behavior | Good (318 tests) |
| **Feature** | `simple/std_lib/test/features/` | Feature documentation + basic tests | Good (116 tests) |
| **System** | `simple/test/system/` | End-to-end workflows | **Gaps identified** |
| **Integration** | `simple/std_lib/test/integration/` | Cross-module integration | Needs expansion |

## Phase 1: Collections System Tests (High Priority)

### 1.1 HashMap Integration Workflows
**File:** `simple/test/system/collections/hashmap_workflows_spec.spl`

**End-to-end scenarios:**

```simple
describe "HashMap real-world workflows":
    context "Word frequency counter":
        it "counts words from text input":
            val text = "hello world hello simple world"
            val freq = HashMap.new()

            for word in text.split(" "):
                val count = freq.get(word) or 0
                freq.insert(word, count + 1)

            expect(freq.get("hello")).to(eq(2))
            expect(freq.get("world")).to(eq(2))
            expect(freq.get("simple")).to(eq(1))

    context "Cache implementation":
        it "implements simple LRU cache with HashMap":
            # Test full cache workflow: insert, lookup, eviction
            # Exercises HashMap + custom logic

    context "Data aggregation":
        it "groups records by key and aggregates values":
            # Test map-reduce style operations
            # Exercises HashMap.each, map_values, filter

    context "Performance benchmarking":
        it "handles 10,000 insertions efficiently":
            # Ensures HashMap FFI bindings work at scale
```

**Coverage impact:** HashMap FFI (hashmap.rs 0%→80%), collections codegen

**Estimated:** 12-15 tests

---

### 1.2 HashSet Integration Workflows
**File:** `simple/test/system/collections/hashset_workflows_spec.spl`

**End-to-end scenarios:**

```simple
describe "HashSet real-world workflows":
    context "Deduplication":
        it "removes duplicate items from list":
            val items = [1, 2, 3, 2, 1, 4, 3, 5]
            val unique = HashSet.new()
            for item in items:
                unique.add(item)

            val result = unique.to_array()
            expect(result.len()).to(eq(5))

    context "Set operations for permissions":
        it "checks user permissions with set operations":
            val user_perms = HashSet.from(["read", "write"])
            val required_perms = HashSet.from(["read", "execute"])

            val has_read = user_perms.intersection(required_perms)
            expect(has_read.contains("read")).to(be_true())

    context "Unique visitor tracking":
        it "tracks unique visitors efficiently":
            # Simulate visitor IDs, test add/contains/len
```

**Coverage impact:** HashSet FFI (hashset.rs 0%→75%)

**Estimated:** 10-12 tests

---

### 1.3 BTreeMap/BTreeSet Workflows
**File:** `simple/test/system/collections/btree_workflows_spec.spl`

**End-to-end scenarios:**

```simple
describe "BTreeMap ordered operations":
    context "Time-series data":
        it "maintains chronological order for events":
            val events = BTreeMap.new()
            events.insert(1704067200, "Event A")  # timestamp keys
            events.insert(1704070800, "Event C")
            events.insert(1704069000, "Event B")

            val chronological = events.keys()
            expect(chronological[0]).to(eq(1704067200))
            expect(chronological[1]).to(eq(1704069000))
            expect(chronological[2]).to(eq(1704070800))

    context "Range queries":
        it "queries events in time range":
            # Test range() method for time-bounded queries

    context "Leaderboard ranking":
        it "maintains sorted scores with BTreeSet":
            # Test ordered iteration for rankings
```

**Coverage impact:** BTreeMap/BTreeSet FFI (btreemap.rs 0%→70%)

**Estimated:** 10-12 tests

---

## Phase 2: Process & System Integration (High Priority)

### 2.1 Process Execution Workflows
**File:** `simple/test/system/process/process_workflows_spec.spl`

**End-to-end scenarios:**

```simple
describe "Process execution workflows":
    context "Command pipeline":
        it "runs command and captures output":
            val result = process.output("echo", ["Hello from process"])
            expect(result.stdout).to(include("Hello from process"))
            expect(result.exit_code).to(eq(0))

    context "Error handling":
        it "captures stderr on command failure":
            val result = process.output("ls", ["/nonexistent"])
            expect(result.exit_code).not_to(eq(0))
            expect(result.stderr).to(include("No such file"))

    context "Process timeout":
        it "terminates long-running process after timeout":
            val start_time = time.now()
            val result = process.run_timeout("sleep", ["5"], 100)
            val elapsed = time.now() - start_time

            expect(elapsed).to(be_less_than(200))
            expect(result.timed_out).to(be_true())

    context "Environment variables":
        it "passes custom environment to subprocess":
            # Test env variable propagation

    context "Working directory":
        it "runs process in specified directory":
            # Test working directory setting
```

**Coverage impact:** process.rs (0%→85%), sys module

**Estimated:** 15-18 tests

---

### 2.2 Process + File I/O Integration
**File:** `simple/test/system/integration/process_file_integration_spec.spl`

**End-to-end scenarios:**

```simple
describe "Process and file I/O integration":
    context "Output redirection":
        it "captures command output to file":
            val result = process.output("ls", ["-la"])
            file.write("/tmp/ls_output.txt", result.stdout)

            val saved = file.read("/tmp/ls_output.txt")
            expect(saved).to(include(result.stdout))

    context "Input from file":
        it "reads file and processes with external command":
            file.write("/tmp/test_input.txt", "line1\nline2\nline3")

            # Count lines with wc
            val input_content = file.read("/tmp/test_input.txt")
            val result = process.output("wc", ["-l"], stdin: input_content)
            expect(result.stdout.trim()).to(eq("3"))

    context "Data transformation pipeline":
        it "chains file read → process → file write":
            # Read CSV → process with external tool → save results
```

**Coverage impact:** process.rs + file I/O FFI integration

**Estimated:** 10-12 tests

---

## Phase 3: Networking System Tests (Medium Priority)

### 3.1 TCP Client-Server Integration
**File:** `simple/test/system/networking/tcp_integration_spec.spl`

**End-to-end scenarios:**

```simple
describe "TCP client-server integration":
    context "Echo server":
        it "starts server, connects client, echoes data":
            # Start TCP listener
            val listener = tcp.TcpListener.bind("127.0.0.1:9999")

            # Accept connection in background
            async:
                val connection = await listener.accept()
                val data = await connection.read(1024)
                await connection.write(data)  # Echo back
                connection.close()

            # Connect client
            val client = await tcp.TcpStream.connect("127.0.0.1:9999")
            await client.write("Hello TCP")
            val response = await client.read(1024)

            expect(response).to(eq("Hello TCP"))
            client.close()

    context "Multiple concurrent connections":
        it "handles multiple clients simultaneously":
            # Test concurrent connection handling

    context "Error handling":
        it "handles connection refused gracefully":
            # Test error cases
```

**Coverage impact:** net_tcp.rs (7.62%→75%), async runtime, monoio integration

**Estimated:** 15-18 tests

---

### 3.2 HTTP Request Integration (if http module exists)
**File:** `simple/test/system/networking/http_integration_spec.spl`

**End-to-end scenarios:**

```simple
describe "HTTP request workflows":
    context "REST API calls":
        it "makes GET request and parses JSON response":
            # Exercises HTTP + JSON parsing

    context "Error handling":
        it "handles 404 errors gracefully":
            # Test HTTP error codes
```

**Coverage impact:** net_http.rs (0%→60%)

**Estimated:** 8-10 tests

---

## Phase 4: Hash Functions Integration

### 4.1 Hash Function Workflows
**File:** `simple/test/system/infrastructure/hash_workflows_spec.spl`

**End-to-end scenarios:**

```simple
describe "Hash function workflows":
    context "Data integrity verification":
        it "computes SHA-256 checksum for file":
            val content = "Important data content"

            val hasher = hash.sha256()
            hasher.update(content)
            val checksum = hasher.finish()

            # Verify deterministic
            val hasher2 = hash.sha256()
            hasher2.update(content)
            expect(hasher2.finish()).to(eq(checksum))

    context "Password hashing":
        it "hashes password with salt":
            # Test bcrypt/argon2 if available

    context "Fast hashing for HashMap":
        it "uses XxHash for non-cryptographic hashing":
            val hasher = hash.xxhash(seed: 42)
            hasher.update("key")
            val hash_value = hasher.finish()

            expect(hash_value).to(be_greater_than(0))
```

**Coverage impact:** hash.rs (0%→70%)

**Estimated:** 12-15 tests

---

## Phase 5: Advanced Integration Workflows

### 5.1 Multi-Module Integration
**File:** `simple/test/system/integration/full_application_spec.spl`

**Complex end-to-end scenarios:**

```simple
describe "Full application workflows":
    context "Web scraper with persistence":
        it "fetches URL, extracts data, stores in HashMap, saves to file":
            # HTTP request → parse HTML → HashMap → file write
            # Exercises: HTTP, string parsing, HashMap, file I/O

    context "Log analyzer":
        it "reads log file, aggregates stats with HashMap, generates report":
            # file read → line parsing → HashMap aggregation → output
            # Exercises: file I/O, HashMap, string manipulation

    context "Concurrent data processing":
        it "spawns worker processes, aggregates results":
            # process spawning → result collection → HashMap merge
            # Exercises: process, async, HashMap
```

**Coverage impact:** Cross-cutting, tests integration between modules

**Estimated:** 15-20 tests

---

### 5.2 Mixin Composition System Tests
**File:** `simple/test/system/mixins/mixin_integration_advanced_spec.spl`

**End-to-end scenarios:**

```simple
describe "Mixin composition in real classes":
    context "Multiple mixin combination":
        it "combines Serializable + Validatable + Timestamped mixins":
            mixin Serializable:
                fn to_json() -> text:
                    # ... implementation

            mixin Validatable:
                fn validate() -> bool:
                    # ... implementation

            class User:
                name: text
                email: text

                include Serializable
                include Validatable

            val user = User(name: "Alice", email: "alice@test.com")
            expect(user.validate()).to(be_true())
            expect(user.to_json()).to(include("Alice"))

    context "Mixin method conflicts":
        it "detects conflicting method names across mixins":
            # Test error detection
```

**Coverage impact:** mixin_checker.rs (0%→75%), dispatch_checker.rs (0%→60%)

**Estimated:** 12-15 tests

---

## Implementation Roadmap

### Week 1: Collections System Tests (37-39 tests)
- HashMap workflows (12-15 tests)
- HashSet workflows (10-12 tests)
- BTreeMap/BTreeSet workflows (10-12 tests)
- **Coverage gain:** +10-12%

### Week 2: Process & Integration (25-30 tests)
- Process workflows (15-18 tests)
- Process + File I/O integration (10-12 tests)
- **Coverage gain:** +8-10%

### Week 3: Networking (23-28 tests)
- TCP integration (15-18 tests)
- HTTP integration (8-10 tests)
- **Coverage gain:** +6-8%

### Week 4: Advanced Integration (39-50 tests)
- Hash workflows (12-15 tests)
- Multi-module integration (15-20 tests)
- Mixin system tests (12-15 tests)
- **Coverage gain:** +8-10%

## Total Impact

| Metric | Current | Target | Gain |
|--------|---------|--------|------|
| **SSpec System Tests** | 131 | 255-278 | +124-147 tests |
| **Rust Coverage** | 58.61% | 75-82% | +16-23% |
| **0% Coverage Modules** | 15 modules | 3-5 modules | 10-12 modules covered |

## System Test Characteristics

All new tests must:
1. ✅ Execute actual Simple code (not just API calls)
2. ✅ Exercise full compilation pipeline (parse → execute)
3. ✅ Integrate multiple modules/components
4. ✅ Test realistic workflows, not isolated functions
5. ✅ Include error/edge cases
6. ✅ Verify both behavior AND integration

## Test Structure Template

```simple
# <Feature> System Integration Spec
"""
## System Test: <Workflow Name>

**Integration Scope:** <Module A> + <Module B> + <Module C>
**Complexity:** Medium/High
**Coverage Impact:** <Rust modules affected>

Tests end-to-end workflows that exercise the full compilation
pipeline and verify component integration.
"""

import std.spec
import <modules to test>

describe "<Workflow Category>":
    context "<Specific scenario>":
        it "<end-to-end test description>":
            # ARRANGE: Setup test data/state
            val data = ...

            # ACT: Execute workflow (multiple steps/modules)
            val result = ...

            # ASSERT: Verify end-to-end behavior
            expect(result).to(...)

            # Optional: CLEANUP
```

## Module-to-Test Mapping

| Rust Module (0% Coverage) | System Test File | Primary Workflow |
|----------------------------|------------------|------------------|
| hashmap.rs | collections/hashmap_workflows_spec.spl | Word frequency, caching |
| hashset.rs | collections/hashset_workflows_spec.spl | Deduplication, permissions |
| btreemap.rs | collections/btree_workflows_spec.spl | Time-series, leaderboards |
| process.rs | process/process_workflows_spec.spl | Command execution, pipelines |
| net_tcp.rs | networking/tcp_integration_spec.spl | Echo server, client-server |
| hash.rs | infrastructure/hash_workflows_spec.spl | Checksums, integrity |
| mixin_checker.rs | mixins/mixin_integration_advanced_spec.spl | Multi-mixin composition |
| dispatch_checker.rs | mixins/mixin_integration_advanced_spec.spl | Method resolution |

## Fixed Issues (This Session)

- ✅ Fixed `lean_golden_spec.spl` - removed unavailable io.fs import
- ✅ Fixed `lean_codegen_spec.spl` - renamed `var` to `mk_var` to avoid keyword conflict
- ✅ Fixed `lean_naming_spec.spl` - replaced unicode escapes with actual guillemet characters
- ✅ Updated `functions.spl` export to use `mk_var` instead of `var`
- ✅ All lean-related tests now pass (6/6 tests)

## Success Criteria

- [ ] 120+ new system tests added
- [ ] Rust coverage reaches 75%+
- [ ] All 0% coverage stdlib modules have >60% coverage
- [ ] All tests exercise full compilation pipeline
- [ ] All tests verify end-to-end workflows
- [ ] Test failures indicate real integration issues
