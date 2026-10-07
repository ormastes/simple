//! The hosted C string facade and seed interpreter expose identical UTF-8 bytes.
use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(source: &str) {
    let module = Parser::new(source).parse().unwrap();
    assert_eq!(interpreter::evaluate_module(&module.items).unwrap(), 0);
}

#[test]
fn registered_string_byte_array_preserves_utf8_and_round_trips() {
    run(r#"extern fn rt_string_to_byte_array(value: text) -> [u8]
extern fn rt_string_from_byte_array(value: [u8]) -> text
val bytes = rt_string_to_byte_array("Aé")
val restored = rt_string_from_byte_array(bytes)
main = if bytes.len() == 3 and bytes[0] == 65 and bytes[1] == 195 and bytes[2] == 169 and restored == "Aé": 0 else: 1
"#);
}

#[test]
fn registered_string_byte_array_returns_a_real_empty_array() {
    run(r#"extern fn rt_string_to_byte_array(value: text) -> [u8]
val bytes = rt_string_to_byte_array("")
main = if bytes.len() == 0: 0 else: 1
"#);
}
