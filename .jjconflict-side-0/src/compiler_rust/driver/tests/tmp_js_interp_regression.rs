mod test_helpers;

#[test]
fn jit_direct_i64_interpolation_after_call_stays_raw() {
    let src = r#"
fn format_id(id: i64) -> text:
    "{id}"

fn consume(a: text, b: text, c: text, d: text):
    print ""

fn main():
    val held_id: i64 = 49
    consume("a", "b", "c", "d")
    print "helper={format_id(held_id)} direct={held_id}"
"#;
    test_helpers::run_on_stdout(test_helpers::Backend::Jit, src, "\nhelper=49 direct=49\n");
}
