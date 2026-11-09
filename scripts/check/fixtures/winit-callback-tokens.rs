use proc_macro2::{Delimiter, TokenStream, TokenTree};
fn named_function(stream: TokenStream, name: &str, found: &mut Vec<TokenStream>) {
    let tokens: Vec<_> = stream.into_iter().collect();
    for (index, token) in tokens.iter().enumerate() {
        if matches!(token, TokenTree::Ident(id) if id == "fn")
            && matches!(tokens.get(index + 1), Some(TokenTree::Ident(id)) if id == name)
        {
            let body = tokens[index + 2..]
                .iter()
                .find_map(|token| match token {
                    TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                        Some(group.stream())
                    }
                    _ => None,
                })
                .expect("function body missing");
            found.push(body);
        }
        if let TokenTree::Group(group) = token {
            named_function(group.stream(), name, found);
        }
    }
}
fn event_match(stream: TokenStream, found: &mut Vec<String>) {
    let tokens: Vec<_> = stream.into_iter().collect();
    for (index, token) in tokens.iter().enumerate() {
        if matches!(token, TokenTree::Ident(id) if id == "match")
            && matches!(tokens.get(index + 1), Some(TokenTree::Ident(id)) if id == "event")
        {
            if let Some(TokenTree::Group(group)) = tokens.get(index + 2) {
                assert_eq!(group.delimiter(), Delimiter::Brace);
                // Includes EVERY arm. Literal spelling and punctuation are retained.
                found.push(group.stream().to_string());
            }
        }
        if let TokenTree::Group(group) = token {
            event_match(group.stream(), found);
        }
    }
}
fn callback(source: &str) -> String {
    let mut functions = Vec::new();
    named_function(
        source.parse().expect("owner tokenization failed"),
        "event_loop_thread_main",
        &mut functions,
    );
    assert_eq!(functions.len(), 1, "event loop owner boundary changed");
    let mut callbacks = Vec::new();
    event_match(functions.pop().unwrap(), &mut callbacks);
    assert_eq!(callbacks.len(), 1, "callback boundary changed");
    callbacks.pop().unwrap()
}
fn negative_controls() {
    let source = r###"fn event_loop_thread_main() {
        run(move |event, target| match event {
            Event::Request => { let ordinary = "a b"; let raw = r##"a b } { "##; let character = ' '; },
            Event::AboutToWait => {},
            _ => {}
        });
    }"###;
    let original = callback(source);
    assert_eq!(
        original,
        callback(&source.replace("match event {", "match\n event\n {"))
    );
    for changed in [
        source.replace("\"a b\"", "\"ab\""),
        source.replace("a b } { ", "ab } { "),
        source.replace("' '", "'x'"),
        source.replace("_ => {}", "_ => { target.exit(); }"),
        source.replace(
            "Event::AboutToWait => {}",
            "Event::AboutToWait => { target.exit(); }",
        ),
        source.replace("_ => {}", ""),
    ] {
        assert_ne!(original, callback(&changed), "changed callback accepted");
    }
    println!("PASS formatting accepted; string/raw/char literal, default/lifecycle changes and removed default rejected");
}
fn main() {
    negative_controls();
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3);
    let old = std::fs::read_to_string(&args[1]).unwrap();
    let new = std::fs::read_to_string(&args[2]).unwrap();
    assert_eq!(
        callback(&old),
        callback(&new),
        "complete original callback tokens changed"
    );
    println!("PASS complete production callback token equivalence including default/lifecycle arms and literal contents");
}
