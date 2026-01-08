Feature: Mixin Type Inference and Constraints
  As a Simple language developer
  I want the compiler to infer types correctly with mixins
  So that generic mixins work seamlessly with type inference

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And type inference is enabled

  Scenario: Infer mixin type from field usage
    Given a file "infer_field.smp" with content:
      """
      mixin Container<T>:
          var items: Vec<T>

      class Box:
          use Container
          
          fn add_number():
              self.items.push(42)  # Infer T = i64
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"
    And field "items" should have type "Vec<i64>"

  Scenario: Infer mixin type from method return
    Given a file "infer_return.smp" with content:
      """
      mixin Producer<T>:
          fn produce() -> T

      class StringProducer:
          use Producer
          
          fn produce() -> String:
              return "hello"  # Infer T = String
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "String"

  Scenario: Infer mixin type from method parameter
    Given a file "infer_param.smp" with content:
      """
      mixin Consumer<T>:
          fn consume(item: T)

      class IntConsumer:
          use Consumer
          
          fn consume(item: i64):
              println(item)  # Infer T = i64
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"

  Scenario: Multiple mixins with interdependent type inference
    Given a file "interdependent.smp" with content:
      """
      mixin Source<T>:
          fn get() -> T

      mixin Sink<T>:
          fn put(value: T)

      class Pipe:
          use Source, Sink
          
          fn transfer():
              let value = self.get()  # Infer T from get
              self.put(value)         # Must match put's T
      """
    When I compile the file with type inference
    Then compilation should succeed
    And both mixin type parameters should be unified

  Scenario: Constrained type inference with trait bounds
    Given a file "bounded_inference.smp" with content:
      """
      mixin Sortable<T> where T: Ord:
          var data: Vec<T>
          
          fn sort():
              self.data.sort()

      class Rankings:
          use Sortable
          
          fn add_score(score: i64):
              self.data.push(score)  # Infer T = i64, check i64: Ord
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"
    And trait bound "Ord" should be verified for "i64"

  Scenario: Failed trait bound should report clear error
    Given a file "bound_violation.smp" with content:
      """
      mixin Comparable<T> where T: Ord:
          fn compare(a: T, b: T) -> i64

      struct Unordered:
          var x: i64
          # No Ord implementation

      class Comparator:
          use Comparable
          
          fn compare(a: Unordered, b: Unordered) -> i64:
              return 0  # Error: Unordered doesn't implement Ord
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "type 'Unordered' does not satisfy trait bound 'Ord'"
    And the error should reference mixin "Comparable"

  Scenario: Inference with nested generic types
    Given a file "nested_inference.smp" with content:
      """
      mixin NestedContainer<T>:
          var nested: Vec<Option<T>>

      class Store:
          use NestedContainer
          
          fn add_maybe(value: i64):
              self.nested.push(Some(value))  # Infer T = i64
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"
    And field "nested" should have type "Vec<Option<i64>>"

  Scenario: Ambiguous type inference should fail
    Given a file "ambiguous.smp" with content:
      """
      mixin Generic<T>:
          var data: Option<T>

      class Ambiguous:
          use Generic
          # No usage of T - cannot infer
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "cannot infer type parameter 'T'"
    And the error should suggest explicit type annotation

  Scenario: Recursive type inference with self-referential constraints
    Given a file "recursive_inference.smp" with content:
      """
      mixin Node<T> where T: Clone:
          var value: T
          var next: Option<Box<T>>

      class LinkedNode:
          use Node
          
          fn set_value(v: String):
              self.value = v.clone()  # Infer T = String
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "String"

  Scenario: Type inference with associated types
    Given a file "associated_inference.smp" with content:
      """
      trait Iterator:
          type Item
          fn next() -> Option<Item>

      mixin Iterable<T> where T: Iterator:
          var iter: T
          
          fn collect_all() -> Vec<T::Item>

      class IntIterator:
          impl Iterator:
              type Item = i64
              fn next() -> Option<i64>

      class Collection:
          use Iterable
          var iter: IntIterator  # Infer T = IntIterator
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "IntIterator"
    And associated type "Item" should resolve to "i64"

  Scenario: Bidirectional type inference with mixins
    Given a file "bidirectional.smp" with content:
      """
      mixin Converter<T, U>:
          fn convert(input: T) -> U

      class ToStringConverter:
          use Converter
          
          fn convert(input: i64) -> String:
              return input.to_string()  # Infer T = i64, U = String
          
          fn use_it():
              let result: String = self.convert(42)
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"
    And type parameter "U" should be inferred as "String"

  Scenario: Higher-rank type inference with mixins
    Given a file "higher_rank.smp" with content:
      """
      mixin Mapper<T>:
          fn map<F>(func: F) -> Vec<T> where F: Fn(T) -> T

      class Numbers:
          use Mapper
          var data: Vec<i64>
          
          fn double_all():
              return self.map(|x| x * 2)  # Infer T = i64
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"

  Scenario: Partial type inference with explicit annotations
    Given a file "partial_inference.smp" with content:
      """
      mixin KeyValue<K, V>:
          var storage: HashMap<K, V>

      class StringMap:
          use KeyValue<String, _>  # K explicit, V inferred
          
          fn put(key: String):
              self.storage.insert(key, 42)  # Infer V = i64
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "K" should be "String"
    And type parameter "V" should be inferred as "i64"

  Scenario: Type inference error should show inference chain
    Given a file "inference_chain.smp" with content:
      """
      mixin Chain<T>:
          fn step1() -> T
          fn step2(x: T) -> T

      class Pipeline:
          use Chain
          
          fn step1() -> i64:
              return 42
          
          fn step2(x: String) -> String:  # Error: conflicts with inferred T = i64
              return x
      """
    When I compile the file
    Then compilation should fail
    And the error should show inference chain: "T inferred as i64 from step1"
    And the error should mention "conflicts with String in step2"
