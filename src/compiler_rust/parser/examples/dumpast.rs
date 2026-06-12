fn main() {
    let path = std::env::args().nth(1).expect("usage: dumpast <file>");
    let src = std::fs::read_to_string(&path).expect("read");
    let mut p = simple_parser::Parser::new(&src);
    match p.parse() {
        Ok(module) => println!("{:#?}", module),
        Err(e) => println!("PARSE_ERR {:?}", e),
    }
}
