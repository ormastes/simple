// Tests for value.rs - included via include!() macro
//
// Split into 3 files for better organization:
// - value_tests_basic.rs: Type names and basic value tests
// - value_tests_async.rs: Generator and Future tests
// - value_tests_pointers.rs: Pointer wrapping and magic constants

#[cfg(test)]
mod tests {
    use super::*;

    include!("value_tests_basic.rs");
    include!("value_tests_async.rs");
    include!("value_tests_pointers.rs");
}
