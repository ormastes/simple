Feature: Mixin and Static Polymorphism Integration
  As a Simple language developer
  I want mixins and static polymorphism to work together
  So that I can build high-performance composable abstractions

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And static dispatch is enabled

  Scenario: Mixin with static trait bound
    Given a file "mixin_static_trait.smp" with content:
      """
      trait Processor:
          fn process()

      mixin Processing<T> where T: bind static Processor:
          var processor: T

          fn run():
              self.processor.process()  # Statically dispatched
      """
    When I compile the file
    Then compilation should succeed
    And method calls should be statically dispatched

  Scenario: Generic mixin with static bind parameter
    Given a file "generic_mixin_static.smp" with content:
      """
      trait Handler:
          fn handle(data: String)

      mixin EventSystem<H>:
          var handler: H

          fn dispatch<T: bind static Handler>(event: T):
              event.handle("data")  # Static dispatch
      """
    When I compile the file
    Then compilation should succeed
    And no vtable should be generated

  Scenario: Mixin providing trait with static impl
    Given a file "mixin_static_impl.smp" with content:
      """
      trait Compute:
          fn compute() -> i64

      mixin ComputeMixin:
          impl Compute:
              fn compute() -> i64:
                  return 42

      fn use_compute<T: bind static Compute>(c: T) -> i64:
          return c.compute()

      class Calculator:
          use ComputeMixin  # Gets static Compute impl

      fn main():
          let result = use_compute(Calculator())  # Static dispatch
      """
    When I compile the file with optimization
    Then compilation should succeed
    And compute call should be inlined
    And result should be constant-folded to 42

  Scenario: Multiple mixins with different dispatch strategies
    Given a file "mixed_dispatch_mixins.smp" with content:
      """
      trait StaticOp:
          fn static_op()

      trait DynamicOp:
          fn dynamic_op()

      mixin StaticMixin<T: bind static StaticOp>:
          var static_handler: T

          fn call_static():
              self.static_handler.static_op()  # Static

      mixin DynamicMixin<T: bind dyn DynamicOp>:
          var dynamic_handler: T

          fn call_dynamic():
              self.dynamic_handler.dynamic_op()  # Dynamic

      class Hybrid:
          use StaticMixin<FastOp>, DynamicMixin<SlowOp>
      """
    When I compile the file
    Then compilation should succeed
    And static_op should use static dispatch
    And dynamic_op should use dynamic dispatch

  Scenario: Mixin composition with static polymorphism
    Given a file "compose_static.smp" with content:
      """
      trait Serialize:
          fn serialize() -> Vec<u8>

      mixin Cacheable<T: bind static Serialize>:
          var cached: Option<Vec<u8>>

          fn get_cached() -> Vec<u8>:
              if self.cached.is_none():
                  self.cached = Some(self.serialize())  # Static call
              return self.cached.unwrap()

      class Document:
          impl Serialize:
              fn serialize() -> Vec<u8>:
                  # Fast serialization
          
          use Cacheable
      """
    When I compile the file with optimization
    Then compilation should succeed
    And serialize call should be inlined
    And no virtual dispatch overhead

  Scenario: Static mixin method prevents dynamic coercion
    Given a file "prevent_coercion.smp" with content:
      """
      trait Action:
          fn act()

      mixin ActionRunner:
          fn run<A: bind static Action>(action: A):
              action.act()  # Must be static

      class Service:
          use ActionRunner

      fn main():
          let s = Service()
          let dyn_action: bind dyn Action = get_action()
          s.run(dyn_action)  # Error: static bind required
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "cannot pass dynamic trait to static parameter"

  Scenario: Mixin with monomorphization per usage
    Given a file "mono_mixin.smp" with content:
      """
      trait Mapper:
          fn map(x: i64) -> i64

      mixin Mappable<M: bind static Mapper>:
          fn apply(data: Vec<i64>) -> Vec<i64>:
              return data.iter().map(|x| M::map(x)).collect()

      class Service:
          use Mappable<DoubleMapper>

      class OtherService:
          use Mappable<TripleMapper>
      """
    When I compile the file
    Then compilation should succeed
    And two monomorphized versions of apply should exist
    And each should be independently optimized

  Scenario: Zero-cost abstraction verification
    Given a file "zero_cost.smp" with content:
      """
      trait Accumulator:
          fn add(value: i64)
          fn total() -> i64

      mixin StaticAccumulate<A: bind static Accumulator>:
          fn process(values: Vec<i64>, acc: A) -> i64:
              for v in values:
                  acc.add(v)
              return acc.total()

      class SumAccumulator:
          var sum: i64
          impl Accumulator:
              fn add(value: i64):
                  self.sum += value
              fn total() -> i64:
                  return self.sum

      class Counter:
          use StaticAccumulate
      """
    When I compile the file with optimization and assembly output
    Then compilation should succeed
    And assembly should show no function calls
    And loop should be unrolled and inlined

  Scenario: Static bind with trait object error message
    Given a file "helpful_error.smp" with content:
      """
      trait Worker:
          fn work()

      mixin WorkRunner<W: bind static Worker>:
          fn run(worker: W)

      class Manager:
          use WorkRunner

      fn main():
          let m = Manager()
          let workers: Vec<bind dyn Worker> = get_workers()
          for w in workers:
              m.run(w)  # Error with helpful message
      """
    When I compile the file
    Then compilation should fail
    And the error should explain static vs dynamic dispatch
    And the error should suggest using "bind dyn" in mixin or static type

  Scenario: Mixin generic parameter inference with static bound
    Given a file "infer_static_bound.smp" with content:
      """
      trait Op:
          fn operate() -> i64

      mixin OpProcessor<T>:
          fn process(op: T) -> i64 where T: bind static Op:
              return op.operate()

      class Service:
          use OpProcessor

          fn run():
              let result = self.process(AddOp())  # Infer T = AddOp
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter should be inferred
    And static dispatch should be verified

  Scenario: Performance regression test
    Given a file "perf_regression.smp" with content:
      """
      trait Calculate:
          fn calc(x: i64) -> i64

      mixin Calculator<C: bind static Calculate>:
          fn compute_sum(calc: C, n: i64) -> i64:
              var sum = 0
              for i in 0..n:
                  sum += calc.calc(i)
              return sum

      class FastCalc:
          impl Calculate:
              fn calc(x: i64) -> i64:
                  return x * 2

      class Processor:
          use Calculator

      benchmark "static mixin dispatch":
          let p = Processor()
          let result = p.compute_sum(FastCalc(), 10000)
      """
    When I compile and benchmark the file
    Then compilation should succeed
    And performance should match hand-written loop
    And no indirect calls should exist in hot path

  Scenario: Mixin documentation with dispatch strategy
    Given a file "doc_dispatch.smp" with content:
      """
      trait Processor:
          fn process()

      /// Uses static dispatch for zero-cost abstraction
      /// Type parameter must be known at compile time
      mixin StaticProcessor<T: bind static Processor>:
          /// Processes using static dispatch - no vtable overhead
          fn run(processor: T):
              processor.process()  # Inlined

      /// Uses dynamic dispatch for flexibility
      mixin DynamicProcessor<T: bind dyn Processor>:
          /// Processes using dynamic dispatch - allows heterogeneous collections
          fn run(processor: T):
              processor.process()  # Vtable call
      """
    When I generate documentation
    Then documentation should explain dispatch differences
    And documentation should show performance characteristics
    And documentation should suggest when to use each

  Scenario: Compile-time dispatch verification in tests
    Given a file "test_dispatch.smp" with content:
      """
      trait Action:
          fn execute() -> i64

      mixin Executor<A: bind static Action>:
          fn run(action: A) -> i64:
              return action.execute()

      #[test]
      fn test_static_dispatch():
          class TestAction:
              impl Action:
                  fn execute() -> i64:
                      return 42

          class TestExecutor:
              use Executor

          let exec = TestExecutor()
          let result = exec.run(TestAction())
          assert_eq!(result, 42)
          
          # Verify static dispatch in test
          assert_no_vtable!(TestAction)
      """
    When I run tests with dispatch verification
    Then tests should pass
    And static dispatch should be verified
