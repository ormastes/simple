use simple_compiler::CompilerPipeline;
use simple_loader::ModuleLoader;

#[test]
fn compile_and_run_main() {
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("main.simple");
    let out_path = dir.path().join("main.smf");

    std::fs::write(&src_path, "main = 0").unwrap();

    let mut compiler = CompilerPipeline::new().unwrap();
    compiler.compile(&src_path, &out_path).unwrap();

    let loader = ModuleLoader::new();
    let module = loader.load(&out_path).unwrap();

    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().expect("main symbol");
    let exit = main();
    assert_eq!(exit, 0);
}
