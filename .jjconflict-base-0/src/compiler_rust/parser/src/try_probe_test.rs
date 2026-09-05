#[cfg(test)]
mod try_probe {
    fn has_try(src: &str) -> bool {
        let module = crate::Parser::new(src).parse().expect("parse");
        format!("{:?}", module.items).contains("Try(")
    }

    #[test]
    fn question_after_call_parses_as_try() {
        assert!(
            has_try("fn f() -> Result<i64, text>:\n    val h = g(10)?\n    Ok(h + 1)\n"),
            "simple shape"
        );
        let full = "fn half(n: i64) -> Result<i64, text>:\n    if n % 2 == 0:\n        return Ok(n / 2)\n    Err(\"odd: {n}\")\n\nfn probe() -> Result<i64, text>:\n    val h = half(10)?\n    print(\"H_IS=[{h}]\")\n    Ok(h)\n\nfn main():\n    match probe():\n        case Ok(v): print(\"P_OK={v}\")\n        case Err(e): print(\"P_ERR={e}\")\nmain()\n";
        assert!(has_try(full), "full f_h.spl shape LOST the Try node");
    }
}
