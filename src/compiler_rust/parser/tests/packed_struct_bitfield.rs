use simple_parser::Parser;

#[test]
fn reject_struct_field_bit_width_with_targeted_diagnostic() {
    let mut parser = Parser::new("@packed\nstruct Flags:\n    mode: u16:4\n");
    let err = parser.parse().expect_err("field bit width is not implemented yet");
    let msg = err.to_string();
    assert!(msg.contains("packed struct bitfield syntax"));
    assert!(msg.contains("field: Type:bits"));
}

#[test]
fn reject_post_name_packed_struct_syntax_with_targeted_diagnostic() {
    let mut parser = Parser::new("struct Flags @packed { mode: u16:4 }\n");
    let err = parser
        .parse()
        .expect_err("post-name @packed syntax is not implemented yet");
    let msg = err.to_string();
    assert!(msg.contains("post-name @packed struct syntax"));
    assert!(msg.contains("not implemented yet"));
}
