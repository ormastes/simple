# Feature: rt_time_now_ns — hosted and baremetal clock extern
# Anchors: rt_time_now_ns extern in src/runtime/ and baremetal stubs
# Target: src/runtime/time.spl (hosted), examples/simple_os/arch/x86_64/boot/baremetal_stubs.c
# Status: pending — wave 7/8 impl must satisfy these contracts.

Feature: rt_time_now_ns returns monotonic nanosecond timestamp on hosted and baremetal targets
  As a benchmarking and scheduling engineer
  I want rt_time_now_ns() to return a monotonically increasing u64 nanosecond count
  So that timing, profiling, and the N4b scrub scheduler can rely on a consistent clock

  Background:
    Given the Simple runtime is compiled for the current target (hosted or baremetal)

  Scenario: Hosted — rt_time_now_ns returns a non-zero value
    Given the process is running under a POSIX host (Linux x86_64)
    When  I call "rt_time_now_ns()"
    Then  the returned u64 is > 0
    And   a second call returns a value >= the first call (monotonic guarantee)

  Scenario: Hosted — two calls separated by a sleep differ by at least 1ms
    Given the process is running under a POSIX host
    When  I call rt_time_now_ns() → t1, sleep 1ms, then call rt_time_now_ns() → t2
    Then  t2 - t1 >= 1_000_000 nanoseconds

  Scenario: Baremetal — rt_time_now_ns uses TSC or hardware timer
    Given the target is SimpleOS baremetal x86_64
    And   the HPET or TSC calibration has been performed during boot
    When  I call "rt_time_now_ns()" from kernel context
    Then  the returned value is derived from the hardware timer (TSC / HPET)
    And   successive calls are monotonically non-decreasing

  Scenario: Baremetal stub compiles and links without POSIX symbols
    Given the baremetal build excludes libc (no clock_gettime symbol)
    When  the kernel image is linked
    Then  rt_time_now_ns resolves to the baremetal_stubs.c implementation
    And   no undefined symbol errors occur at link time

  Scenario: rt_time_now_ns is usable before heap allocation
    Given the Simple runtime has not yet initialized the allocator
    When  rt_time_now_ns() is called (e.g. from an early boot timing probe)
    Then  it returns a valid timestamp without triggering an allocator call
    And   the call does not panic or trap
