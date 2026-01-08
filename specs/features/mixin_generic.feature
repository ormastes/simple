Feature: Generic Mixins with Type Parameters
  As a Simple language developer
  I want to use generic type parameters in mixins
  So that mixins can work with different types and the compiler infers them

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And type inference is enabled

  Scenario: Declare generic mixin with one type parameter
    Given a file "cache.smp" with content:
      """
      mixin Cache<T>:
          var cache: HashMap<String, T>

          fn get_cached(key: String) -> Option<T>:
              return self.cache.get(key)

          fn set_cache(key: String, value: T):
              self.cache.insert(key, value)
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have type parameter "T"
    And field "cache" should have type "HashMap<String, T>"

  Scenario: Apply generic mixin with explicit type argument
    Given a file "user_service.smp" with content:
      """
      mixin Cache<T>:
          var cache: HashMap<String, T>

          fn get_cached(key: String) -> Option<T>
          fn set_cache(key: String, value: T)

      class UserService:
          use Cache<User>  # Explicit type argument

          fn get_user(id: i64) -> Option<User>:
              return self.get_cached(id.to_string())
      """
    When I compile the file
    Then compilation should succeed
    And class "UserService" should have field "cache" of type "HashMap<String, User>"
    And method "get_cached" should return type "Option<User>"

  Scenario: Infer generic type parameter from usage
    Given a file "inferred_cache.smp" with content:
      """
      mixin Cache<T>:
          var cache: HashMap<String, T>

          fn get_cached(key: String) -> Option<T>
          fn set_cache(key: String, value: T)

      class ProductService:
          use Cache  # No explicit type arg - infer from usage

          fn get_product(id: i64) -> Option<Product>:
              let key = id.to_string()
              if let Some(product) = self.get_cached(key):
                  return Some(product)  # Infer T = Product here
              # ...
      """
    When I compile the file with type inference
    Then compilation should succeed
    And the mixin type parameter "T" should be inferred as "Product"
    And field "cache" should have inferred type "HashMap<String, Product>"

  Scenario: Multiple generic type parameters
    Given a file "repository.smp" with content:
      """
      mixin Repository<T, E>:
          required fn connection() -> DbConnection

          fn find_by_id(id: i64) -> Result<T, E>:
              let conn = self.connection()
              # Implementation...

          fn save(entity: T) -> Result<(), E>:
              # Implementation...
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have type parameters "T" and "E"
    And method "find_by_id" should return type "Result<T, E>"
    And method "save" should take parameter of type "T"

  Scenario: Generic mixin with trait bounds
    Given a file "serializable_cache.smp" with content:
      """
      mixin SerializableCache<T> where T: Serialize + Deserialize:
          var cache: HashMap<String, T>

          fn save_to_disk(path: String):
              let json = self.cache.to_json()  # Uses Serialize trait
              write_file(path, json)

          fn load_from_disk(path: String):
              let json = read_file(path)
              self.cache = HashMap::from_json(json)  # Uses Deserialize trait
      """
    When I parse the file
    Then parsing should succeed
    And type parameter "T" should have trait bound "Serialize"
    And type parameter "T" should have trait bound "Deserialize"

  Scenario: Apply generic mixin with trait bounds
    Given a file "user_cache.smp" with content:
      """
      mixin SerializableCache<T> where T: Serialize:
          var cache: HashMap<String, T>
          fn save_to_disk(path: String)

      class User:
          impl Serialize  # User implements required trait

      class UserCache:
          use SerializableCache<User>  # Valid: User implements Serialize
      """
    When I compile the file
    Then compilation should succeed

  Scenario: Generic mixin with trait bound violation should fail
    Given a file "invalid_trait_bound.smp" with content:
      """
      mixin SerializableCache<T> where T: Serialize:
          var cache: HashMap<String, T>

      class Session:
          # Session does NOT implement Serialize

      class SessionCache:
          use SerializableCache<Session>  # Error: Session doesn't implement Serialize
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "type 'Session' does not implement trait 'Serialize'"

  Scenario: Nested generic types in mixin
    Given a file "nested_generics.smp" with content:
      """
      mixin AsyncQueue<T>:
          var queue: Vec<Future<T>>

          fn push_async(future: Future<T>):
              self.queue.push(future)

          fn poll_next() -> Option<Future<T>>:
              return self.queue.pop()
      """
    When I parse the file
    Then parsing should succeed
    And field "queue" should have type "Vec<Future<T>>"
    And method "push_async" should take parameter of type "Future<T>"

  Scenario: Generic mixin with default type parameter
    Given a file "default_type_param.smp" with content:
      """
      mixin Logger<T = String>:
          var log: Vec<T>

          fn add_log(entry: T):
              self.log.push(entry)
      """
    When I parse the file
    Then parsing should succeed
    And type parameter "T" should have default type "String"

  Scenario: Apply mixin with default type parameter
    Given a file "use_default_param.smp" with content:
      """
      mixin Logger<T = String>:
          var log: Vec<T>

      class Service:
          use Logger  # Uses default T = String
      """
    When I compile the file
    Then compilation should succeed
    And field "log" should have type "Vec<String>"

  Scenario: Multiple generic mixins on same class
    Given a file "multiple_generic_mixins.smp" with content:
      """
      mixin Cache<T>:
          var cache: HashMap<String, T>

      mixin Logger<L>:
          var log: Vec<L>

      class DataService:
          use Cache<User>, Logger<String>
          var data: Vec<User>
      """
    When I compile the file
    Then compilation should succeed
    And field "cache" should have type "HashMap<String, User>"
    And field "log" should have type "Vec<String>"

  Scenario: Type parameter shadows class type parameter
    Given a file "shadow_type_param.smp" with content:
      """
      mixin Cache<T>:
          var cache: HashMap<String, T>

      class Container<T>:  # Different T
          use Cache<User>  # Mixin's T is User, not Container's T
          var items: Vec<T>  # This T is Container's type parameter
      """
    When I compile the file
    Then compilation should succeed
    And the mixin "Cache" type parameter should be "User"
    And the class "Container" type parameter should remain independent
