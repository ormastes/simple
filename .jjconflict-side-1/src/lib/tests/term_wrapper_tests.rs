use simple_native_loader::ModuleLoader;
use simple_term_io::io::term::TermNative;

#[test]
fn native_loader_calls_symbol_directly() {
    let path = std::path::PathBuf::from(env!("TERM_NATIVE_LIB"));
    let module = ModuleLoader::new()
        .load(&path)
        .expect("native lib should load");

    type AddFn = unsafe extern "C" fn(i64, i64) -> i64;
    let add: AddFn = module
        .get_function("term_add")
        .expect("term_add symbol available");
    let result = unsafe { add(4, 5) };
    assert_eq!(result, 9);
}

#[test]
fn wrapper_calls_native_functions() {
    let term = TermNative::load().expect("wrapper loads native lib");
    assert_eq!(term.add(2, 3), Some(5));
    assert_eq!(term.strlen("hello"), Some(5));
}
