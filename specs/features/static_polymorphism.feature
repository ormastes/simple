Feature: Static Polymorphism with Bind Statement
  As a Simple language developer
  I want to use static polymorphism for zero-cost abstractions
  So that I can write generic code without runtime overhead

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And static dispatch is enabled

  Scenario: Basic static bind with trait
    Given a file "static_bind.smp" with content:
      """
      trait Drawable:
          fn draw()

      class Circle:
          impl Drawable:
              fn draw():
                  println("Drawing circle")

      fn render(obj: bind static Drawable):
          obj.draw()
      """
    When I compile the file
    Then compilation should succeed
    And function "render" should use static dispatch
    And no vtable should be generated for "Drawable"

  Scenario: Dynamic bind is default behavior
    Given a file "dynamic_default.smp" with content:
      """
      trait Shape:
          fn area() -> f64

      fn calculate_area(shape: bind Shape) -> f64:
          return shape.area()
      """
    When I compile the file
    Then compilation should succeed
    And function "calculate_area" should use dynamic dispatch
    And a vtable should be generated for "Shape"

  Scenario: Explicit dynamic bind
    Given a file "explicit_dynamic.smp" with content:
      """
      trait Printable:
          fn print()

      fn show(obj: bind dyn Printable):
          obj.print()
      """
    When I compile the file
    Then compilation should succeed
    And function "show" should use dynamic dispatch

  Scenario: Static bind with multiple trait bounds
    Given a file "multi_static_bounds.smp" with content:
      """
      trait Clone:
          fn clone() -> Self

      trait Debug:
          fn debug() -> String

      fn process<T>(item: bind static Clone + Debug):
          let copy = item.clone()
          println(copy.debug())
      """
    When I compile the file
    Then compilation should succeed
    And all trait calls should be statically dispatched
    And function should be monomorphized per concrete type

  Scenario: Static bind performance - no heap allocation
    Given a file "zero_cost.smp" with content:
      """
      trait Counter:
          fn increment()

      class LocalCounter:
          var count: i64
          impl Counter:
              fn increment():
                  self.count += 1

      fn run_counter(c: bind static Counter):
          c.increment()  # Stack-only, no heap allocation
      """
    When I compile the file with optimization
    Then compilation should succeed
    And no heap allocation should occur in "run_counter"
    And the call should be inlined

  Scenario: Static bind with generic type inference
    Given a file "infer_static.smp" with content:
      """
      trait Numeric:
          fn add(other: Self) -> Self

      fn sum_twice<T>(a: T, b: T) -> T where T: bind static Numeric:
          let first = a.add(b)
          return first.add(first)
      """
    When I compile the file
    Then compilation should succeed
    And monomorphization should generate separate versions per type
    And no trait objects should be created

  Scenario: Mix static and dynamic dispatch
    Given a file "mixed_dispatch.smp" with content:
      """
      trait Worker:
          fn work()

      fn process_static(w: bind static Worker):
          w.work()  # Statically dispatched

      fn process_dynamic(w: bind dyn Worker):
          w.work()  # Dynamically dispatched

      fn orchestrate(workers: Vec<bind dyn Worker>):
          for worker in workers:
              process_dynamic(worker)  # Can't use static - heterogeneous collection
      """
    When I compile the file
    Then compilation should succeed
    And "process_static" should not generate vtable
    And "process_dynamic" should use vtable
    And "workers" collection should use trait objects

  Scenario: Static bind with associated types
    Given a file "static_associated.smp" with content:
      """
      trait Container:
          type Item
          fn get(index: usize) -> Option<Item>

      fn first_item<C>(container: C) -> Option<C::Item> 
        where C: bind static Container:
          return container.get(0)
      """
    When I compile the file
    Then compilation should succeed
    And associated type should be resolved at compile time
    And no type erasure should occur

  Scenario: Static bind constraint violation
    Given a file "static_violation.smp" with content:
      """
      trait Action:
          fn execute()

      class DynamicAction:
          impl Action:
              fn execute():
                  println("action")

      fn run(action: bind static Action):
          action.execute()

      fn main():
          let actions: Vec<bind dyn Action> = vec![DynamicAction()]
          run(actions[0])  # Error: can't pass dyn to static parameter
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "cannot pass dynamic trait object to static bind parameter"

  Scenario: Static bind with Sized trait
    Given a file "sized_static.smp" with content:
      """
      trait Processor:
          fn process()

      fn handle<T: bind static Processor + Sized>(item: T):
          item.process()  # T is known size - can be stack allocated
      """
    When I compile the file
    Then compilation should succeed
    And parameter "item" should be stack-allocated

  Scenario: Cannot use unsized types with static bind
    Given a file "unsized_static.smp" with content:
      """
      trait Display:
          fn display()

      fn show(item: bind static Display):  # Error: Display is not Sized
          item.display()
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "static bind requires Sized trait bound"

  Scenario: Static bind with higher-rank trait bounds
    Given a file "hrtb_static.smp" with content:
      """
      trait Fn<'a>:
          type Output
          fn call(arg: &'a str) -> Self::Output

      fn apply<F>(func: F, input: &str) 
        where F: for<'a> bind static Fn<'a, Output=i64>:
          return func.call(input)
      """
    When I compile the file
    Then compilation should succeed
    And higher-rank bounds should be statically resolved

  Scenario: Monomorphization code size check
    Given a file "code_size.smp" with content:
      """
      trait Op:
          fn operate() -> i64

      fn compute<T: bind static Op>(op: T) -> i64:
          return op.operate() * 2

      fn main():
          compute(OpA())  # Generates compute_OpA
          compute(OpB())  # Generates compute_OpB
          compute(OpC())  # Generates compute_OpC
      """
    When I compile the file
    Then compilation should succeed
    And three monomorphized versions of "compute" should exist
    And each version should be optimized independently

  Scenario: Static bind with recursive trait bounds
    Given a file "recursive_bound.smp" with content:
      """
      trait Recursive where Self: Sized:
          fn recurse(depth: i64) -> Self

      fn build<T: bind static Recursive>(depth: i64) -> T:
          return T::recurse(depth)
      """
    When I compile the file
    Then compilation should succeed
    And recursive bounds should be properly checked

  Scenario: Compare static vs dynamic dispatch performance
    Given a file "perf_compare.smp" with content:
      """
      trait Math:
          fn calculate(x: i64) -> i64

      fn static_loop(m: bind static Math, n: i64) -> i64:
          var sum = 0
          for i in 0..n:
              sum += m.calculate(i)
          return sum

      fn dynamic_loop(m: bind dyn Math, n: i64) -> i64:
          var sum = 0
          for i in 0..n:
              sum += m.calculate(i)
          return sum
      """
    When I compile the file with benchmarking
    Then compilation should succeed
    And "static_loop" should be faster than "dynamic_loop"
    And "static_loop" should inline "calculate" calls
