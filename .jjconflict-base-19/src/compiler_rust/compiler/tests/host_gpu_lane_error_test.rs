use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;
use simple_runtime::host_gpu_lane;

fn parse_and_eval(source: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut parser = Parser::new(source);
    let module = parser.parse()?;
    Ok(evaluate_module(&module.items)?)
}

#[test]
fn gpu_lane_records_end_when_body_errors() {
    host_gpu_lane::rt_host_gpu_lane_reset();
    host_gpu_lane::rt_host_gpu_queue_reset();

    let source = r#"
class Target:
    fn later():
        pass_do_nothing("lane error probe")

val target = Target()
target.later() gpu \:
    missing_gpu_lane_body_call()

main = 0
"#;

    assert!(parse_and_eval(source).is_err());
    assert_eq!(host_gpu_lane::rt_host_gpu_lane_begin_count(), 1);
    assert_eq!(host_gpu_lane::rt_host_gpu_lane_end_count(), 1);
}
