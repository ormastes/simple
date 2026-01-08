Feature: Static Polymorphism Advanced Scenarios
  As a Simple language developer
  I want advanced static polymorphism features
  So that I can build high-performance zero-cost abstractions

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And static dispatch is enabled

  Scenario: Static bind with const generics
    Given a file "const_generic_static.smp" with content:
      """
      trait FixedSize:
          const SIZE: usize
          fn size() -> usize:
              return Self::SIZE

      class Array16:
          impl FixedSize:
              const SIZE: usize = 16

      fn process<T: bind static FixedSize>(data: T):
          let s = T::SIZE  # Compile-time constant
      """
    When I compile the file
    Then compilation should succeed
    And SIZE should be resolved at compile time

  Scenario: Specialization with static bind
    Given a file "specialization.smp" with content:
      """
      trait Processor:
          fn process(data: Vec<u8>)

      fn optimize<T: bind static Processor>(proc: T):
          proc.process(vec![])  # Can be specialized per type

      class FastProcessor:
          impl Processor:
              fn process(data: Vec<u8>):
                  # SIMD optimized

      class SlowProcessor:
          impl Processor:
              fn process(data: Vec<u8>):
                  # Generic implementation
      """
    When I compile the file with optimization
    Then compilation should succeed
    And FastProcessor version should use SIMD
    And each version should be independently optimized

  Scenario: Zero-cost trait aliasing with static bind
    Given a file "trait_alias.smp" with content:
      """
      trait Numeric = Add + Sub + Mul + Div

      fn compute<T: bind static Numeric>(a: T, b: T) -> T:
          return (a + b) * (a - b) / b
      """
    When I compile the file
    Then compilation should succeed
    And all operations should be inlined
    And no trait object overhead should exist

  Scenario: Static bind with phantom types
    Given a file "phantom.smp" with content:
      """
      trait State:
          # Phantom - no methods

      class Locked:
          impl State

      class Unlocked:
          impl State

      class Resource<S: bind static State>:
          var data: String

          fn process() where S = Unlocked:
              # Only available in Unlocked state
              self.data = "processed"
      """
    When I compile the file
    Then compilation should succeed
    And state should be checked at compile time

  Scenario: Static dispatch with trait object coercion prevention
    Given a file "no_coercion.smp" with content:
      """
      trait Worker:
          fn work()

      fn static_work<T: bind static Worker>(w: T):
          w.work()

      fn try_coerce(w: bind dyn Worker):
          static_work(w)  # Error: cannot coerce dyn to static
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "cannot convert dynamic trait object to static"

  Scenario: Compile-time function resolution with static bind
    Given a file "compile_time_resolution.smp" with content:
      """
      trait Compute:
          fn compute() -> i64

      class AddCompute:
          impl Compute:
              fn compute() -> i64:
                  return 1 + 1

      fn run<T: bind static Compute>() -> i64:
          return T::compute()  # Resolved at compile time

      const RESULT: i64 = run::<AddCompute>()  # Const evaluation
      """
    When I compile the file
    Then compilation should succeed
    And RESULT should be computed at compile time

  Scenario: Static bind with lifetime parameters
    Given a file "lifetime_static.smp" with content:
      """
      trait Borrower<'a>:
          fn borrow(&'a self) -> &'a str

      fn use_borrowed<'a, T: bind static Borrower<'a>>(b: &'a T) -> &'a str:
          return b.borrow()
      """
    When I compile the file
    Then compilation should succeed
    And lifetime parameters should be correctly tracked

  Scenario: Monomorphization limit detection
    Given a file "mono_limit.smp" with content:
      """
      trait Op:
          fn op()

      fn recursive<T: bind static Op>(depth: i64):
          if depth > 0:
              recursive::<T>(depth - 1)
      """
    When I compile the file
    Then compilation should succeed
    And monomorphization should not infinitely recurse

  Scenario: Static bind with negative trait bounds
    Given a file "negative_bound.smp" with content:
      """
      trait Special:
          fn special()

      fn only_non_special<T: bind static !Special>(item: T):
          # Only accepts types that DON'T implement Special
      """
    When I compile the file
    Then compilation should succeed
    And negative bounds should be checked

  Scenario: Cross-crate static dispatch optimization
    Given files "lib.smp" and "main.smp" with content:
      """
      # lib.smp
      pub trait Processor:
          fn process(x: i64) -> i64

      pub fn process_all<T: bind static Processor>(p: T, n: i64) -> i64:
          var sum = 0
          for i in 0..n:
              sum += p.process(i)
          return sum
      """
      """
      # main.smp
      import lib::*

      class DoubleProcessor:
          impl Processor:
              fn process(x: i64) -> i64:
                  return x * 2

      fn main():
          let result = process_all(DoubleProcessor(), 1000)
      """
    When I compile both files with LTO
    Then compilation should succeed
    And inlining should cross crate boundaries

  Scenario: Static bind with auto traits
    Given a file "auto_traits.smp" with content:
      """
      auto trait Send:
          # Automatically implemented by types

      fn send_data<T: bind static Send>(data: T):
          # Guaranteed Send at compile time
      """
    When I compile the file
    Then compilation should succeed
    And Send should be checked at compile time

  Scenario: Static bind prevents trait object size overhead
    Given a file "size_check.smp" with content:
      """
      trait Data:
          fn get() -> i64

      fn static_size<T: bind static Data>() -> usize:
          return size_of::<T>()  # Concrete size

      fn dynamic_size() -> usize:
          return size_of::<bind dyn Data>()  # Fat pointer size
      """
    When I compile the file
    Then compilation should succeed
    And static_size should be smaller than dynamic_size

  Scenario: Blanket implementation with static bind
    Given a file "blanket.smp" with content:
      """
      trait Display:
          fn display() -> String

      impl<T: ToString> Display for T:
          fn display() -> String:
              return self.to_string()

      fn show<T: bind static Display>(item: T):
          println(item.display())
      """
    When I compile the file
    Then compilation should succeed
    And blanket impl should be monomorphized

  Scenario: Static bind with object safety violations allowed
    Given a file "object_unsafe.smp" with content:
      """
      trait Generic<T>:
          fn process(item: T) -> T  # Not object safe

      fn use_generic<T, U: bind static Generic<T>>(g: U, item: T) -> T:
          return g.process(item)  # OK with static - not making trait object
      """
    When I compile the file
    Then compilation should succeed
    And object safety should not be required for static bind

  Scenario: Performance comparison documentation
    Given a file "perf_doc.smp" with content:
      """
      trait Calc:
          fn calc(x: i64) -> i64

      /// Static dispatch - zero overhead
      fn static_calc<T: bind static Calc>(c: T, x: i64) -> i64:
          return c.calc(x)  # Direct call, can inline

      /// Dynamic dispatch - virtual call overhead
      fn dynamic_calc(c: bind dyn Calc, x: i64) -> i64:
          return c.calc(x)  # Vtable lookup
      """
    When I generate documentation
    Then documentation should explain performance difference
    And examples should show assembly difference
