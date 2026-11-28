use simple_parser::Parser;

use super::parse_and_lower;

fn eval_source(source: &str) -> Result<i32, String> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().map_err(|e| format!("parse error: {e:?}"))?;
    crate::interpreter::evaluate_module(&ast.items).map_err(|e| e.to_string())
}

fn lower_err(source: &str) -> String {
    match parse_and_lower(source) {
        Ok(_) => panic!("expected HIR lowering error, succeeded for:\n{source}"),
        Err(e) => e.to_string(),
    }
}

fn eval_err(source: &str) -> String {
    match eval_source(source) {
        Ok(code) => panic!("expected interpreter error, succeeded ({code}) for:\n{source}"),
        Err(e) => e,
    }
}

#[test]
fn hir_rejects_some_none_nil_patterns_on_non_option_scrutinees() {
    let cases = [
        "fn main() -> i64:\n    val x: i64 = 6\n    match x:\n        case Some(v): v\n        case _: 0\n",
        "fn main() -> i64:\n    val x: i64 = 6\n    match x:\n        case None: 1\n        case _: 0\n",
        "fn main() -> i64:\n    val x: i64 = 6\n    match x:\n        case Option.Some(v): v\n        case _: 0\n",
        "fn main() -> i64:\n    val x: i64 = 6\n    match x:\n        case nil: 1\n        case _: 0\n",
        "fn main() -> i64:\n    val x: i64 = 6\n    if val Some(j) = x:\n        return j\n    0\n",
        "fn main() -> i64:\n    var x: i64 = 6\n    while val Some(j) = x:\n        return j\n    0\n",
        "fn main() -> i64:\n    val s: text = \"hello\"\n    match s:\n        case Some(_): 1\n        case _: 0\n",
        "fn main() -> i64:\n    val xs = [1, 2]\n    match xs:\n        case Some(_): 1\n        case _: 0\n",
        "fn main() -> i64:\n    val pair = (1, 2)\n    match pair:\n        case Some(_): 1\n        case _: 0\n",
        "fn main() -> i64:\n    val d = {\"a\": 1}\n    match d:\n        case Some(_): 1\n        case _: 0\n",
        "struct Pt:\n    x: i64\nfn main() -> i64:\n    val p = Pt(x: 1)\n    match p:\n        case Some(_): 1\n        case _: 0\n",
        "enum Color:\n    Red\n    Blue\nfn main() -> i64:\n    val c = Color.Red\n    match c:\n        case Some(_): 1\n        case _: 0\n",
        "enum Color:\n    Red\n    Blue\nfn main() -> i64:\n    val c = Color.Red\n    match c:\n        case nil: 1\n        case _: 0\n",
        "fn main() -> i64:\n    val r: Result<i64, text> = Ok(1)\n    match r:\n        case Some(v): v\n        case _: 0\n",
    ];
    for src in cases {
        let msg = lower_err(src);
        assert!(msg.contains("SPL-PAT-001"), "unexpected diagnostic `{msg}` for:\n{src}");
    }
}

#[test]
fn hir_rejects_option_methods_and_unwrap_or_mismatches() {
    let cases = [
        "fn main() -> i64:\n    6.unwrap_or(-99)\n",
        "fn main() -> i64:\n    6.unwrap()\n",
        "fn main() -> i64:\n    6.expect(\"nope\")\n",
        "fn main() -> bool:\n    6.is_some()\n",
        "fn main() -> bool:\n    6.is_none()\n",
        "fn main() -> text:\n    \"hi\".unwrap_or(\"fallback\")\n",
        "fn main() -> i64:\n    val xs = [1, 2]\n    xs.unwrap_or([0])[0]\n",
        "struct Pt:\n    x: i64\nfn main() -> i64:\n    val p = Pt(x: 1)\n    p.unwrap_or(p).x\n",
        "fn main() -> bool:\n    val r: Result<i64, text> = Ok(1)\n    r.is_some()\n",
        "fn main() -> bool:\n    val r: Result<i64, text> = Ok(1)\n    r.is_none()\n",
        "fn main() -> i64:\n    val o: i64? = 42\n    o.unwrap_or(\"bad\")\n",
    ];
    for src in cases {
        let msg = lower_err(src);
        assert!(msg.contains("SPL-PAT-001"), "unexpected diagnostic `{msg}` for:\n{src}");
    }
}

#[test]
fn hir_accepts_valid_option_custom_enum_array_and_generic_patterns() {
    let cases = [
        "fn main() -> i64:\n    val o: i64? = 42\n    o.unwrap_or(-99)\n",
        "fn main() -> i64:\n    val o: i64? = nil\n    match o:\n        case Some(v): v\n        case nil: -1\n",
        "fn main() -> i64:\n    val o: i64? = 42\n    if val Some(v) = o:\n        return v\n    0\n",
        "enum CustomOpt:\n    Some(i64)\n    None\nfn main() -> i64:\n    val c = CustomOpt.Some(7)\n    match c:\n        case Some(v): v\n        case None: 0\n",
        "fn main() -> i64:\n    val xs = [10, 20]\n    xs.pop().unwrap_or(0)\n",
        "fn dyn_check(o: Any) -> i64:\n    match o:\n        case Some(v): 1\n        case _: 5\n",
        "fn gen_check<T>(o: T) -> i64:\n    match o:\n        case Some(_): 1\n        case _: 0\n",
        "struct CustomWrap:\n    v: i64\n    fn unwrap_or(self, d: i64) -> i64:\n        self.v + d\nfn main() -> i64:\n    val w = CustomWrap(v: 3)\n    w.unwrap_or(4)\n",
        "fn main() -> i64:\n    val r = Ok(9)\n    r.unwrap_or(0)\n",
    ];
    for src in cases {
        parse_and_lower(src).unwrap_or_else(|e| panic!("expected HIR pass, got `{e}` for:\n{src}"));
    }
}

#[test]
fn interpreter_rejects_option_patterns_and_methods_on_non_options() {
    let cases = [
        "fn main() -> i64:\n    match 6:\n        case Some(v): v\n        case _: 0\n",
        "fn main() -> i64:\n    6.unwrap_or(-99)\n",
        "fn main() -> i64:\n    if val Some(j) = 6:\n        return j\n    0\n",
        "fn main() -> i64:\n    match [1, 2]:\n        case Some(_): 1\n        case _: 0\n",
        "struct InterpPt:\n    x: i64\nfn main() -> i64:\n    val p = InterpPt(x: 1)\n    match p:\n        case Some(_): 1\n        case _: 0\n",
        "fn main() -> i64:\n    val o: i64? = 42\n    o.unwrap_or(\"bad\")\n",
        "enum InterpColor:\n    Red\n    Blue\nfn main() -> i64:\n    val c = InterpColor.Red\n    match c:\n        case Some(_): 1\n        case _: 0\n",
        "fn main() -> i64:\n    val r = Ok(1)\n    match r:\n        case Some(v): v\n        case _: 0\n",
        "fn main() -> bool:\n    val r = Ok(1)\n    r.is_some()\n",
    ];
    for src in cases {
        let msg = eval_err(src);
        assert!(msg.contains("SPL-PAT-001"), "unexpected interpreter error `{msg}` for:\n{src}");
    }
}

#[test]
fn interpreter_preserves_valid_option_custom_enum_and_dynamic_cases() {
    let opt_some = "\
fn main() -> i64:
    val w86_o: i64? = 42
    w86_o.unwrap_or(-99)
";
    assert_eq!(eval_source(opt_some).expect("valid i64? unwrap_or"), 42);

    let opt_nil = "\
fn main() -> i64:
    val w86_o: i64? = nil
    w86_o.unwrap_or(7)
";
    assert_eq!(eval_source(opt_nil).expect("valid nil unwrap_or"), 7);

    let custom_wrap = "\
struct W86Wrap:
    v: i64
    fn unwrap_or(self, d: i64) -> i64:
        self.v + d
fn main() -> i64:
    val w = W86Wrap(v: 5)
    w.unwrap_or(4)
";
    assert_eq!(eval_source(custom_wrap).expect("valid custom unwrap_or"), 9);

    let custom_enum = "\
enum W86Opt:
    Some(i64)
    None
fn main() -> i64:
    val c = W86Opt.Some(11)
    match c:
        case Some(v): v
        case None: 0
";
    assert_eq!(eval_source(custom_enum).expect("valid custom Some/None enum"), 11);

    let dynamic_fn = "\
fn w86_dyn(o) -> i64:
    match o:
        case Some(x): 1
        case _: 5
fn main() -> i64:
    w86_dyn(nil)
";
    assert_eq!(eval_source(dynamic_fn).expect("untyped dynamic fn"), 5);

    let array_pop = "\
fn main() -> i64:
    var xs = [12, 34]
    xs.pop().unwrap_or(0)
";
    assert_eq!(eval_source(array_pop).expect("array pop unwrap_or"), 34);
}

#[test]
fn enum_static_methods_returning_option_remain_allowed_while_variants_reject() {
    let valid_annotated = "\
enum W86Parse:
    IntLit
    StrLit
    static fn parse(s: text) -> W86Parse?:
        if s == \"int\":
            return Some(W86Parse.IntLit)
        if s == \"str\":
            return Some(W86Parse.StrLit)
        None
fn main() -> i64:
    var total = 0
    if val Some(tok) = W86Parse.parse(\"int\"):
        match tok:
            case W86Parse.IntLit: total = total + 1
            case _: total = total + 10
    match W86Parse.parse(\"none\"):
        case Some(_): total = total + 100
        case None: total = total + 2
    val unwrapped = W86Parse.parse(\"str\").unwrap()
    match unwrapped:
        case W86Parse.StrLit: total = total + 4
        case _: total = total + 100
    val defaulted = W86Parse.parse(\"none\").unwrap_or(W86Parse.IntLit)
    match defaulted:
        case W86Parse.IntLit: total = total + 8
        case _: total = total + 100
    if W86Parse.parse(\"int\").is_some():
        total = total + 16
    total
";
    assert!(parse_and_lower(valid_annotated).is_ok(), "annotated enum static Option method should lower");
    assert_eq!(eval_source(valid_annotated).expect("annotated enum static Option method eval"), 31);

    let valid_unannotated = "\
enum W86ParseU:
    IntLit
    StrLit
    static fn try_parse(s: text):
        if s == \"int\":
            return Some(W86ParseU.IntLit)
        None
fn main() -> i64:
    var total = 0
    if W86ParseU.try_parse(\"bad\").is_none():
        total = total + 1
    match W86ParseU.try_parse(\"int\").unwrap():
        case W86ParseU.IntLit: total = total + 2
        case _: total = total + 10
    total
";
    assert!(parse_and_lower(valid_unannotated).is_ok(), "unannotated enum static method returning Option should lower");
    assert_eq!(eval_source(valid_unannotated).expect("unannotated enum static method eval"), 3);

    let invalid_variant_cases = [
        "\
enum W86ParseV:
    IntLit
    StrLit
    static fn parse(s: text) -> W86ParseV?:
        None
fn main() -> i64:
    val v = W86ParseV.IntLit
    match v:
        case Some(_): 1
        case _: 0
",
        "\
enum W86ParseV:
    IntLit
    StrLit
    static fn parse(s: text) -> W86ParseV?:
        None
fn main() -> i64:
    val v = W86ParseV.IntLit.unwrap_or(W86ParseV.StrLit)
    0
",
    ];
    for src in invalid_variant_cases {
        let hir_msg = lower_err(src);
        assert!(hir_msg.contains("SPL-PAT-001"), "unexpected HIR diagnostic `{hir_msg}` for:\n{src}");
        let eval_msg = eval_err(src);
        assert!(eval_msg.contains("SPL-PAT-001"), "unexpected eval diagnostic `{eval_msg}` for:\n{src}");
    }
}

#[test]
fn array_and_dict_optional_accessors_preserve_optional_receiver_semantics() {
    let valid_combined = "\
fn main() -> i64:
    val nums: [i64] = [10, 20, 30]
    val words: [text] = [\"alpha\", \"beta\"]
    val flags: [bool] = [true, false]
    val d: Dict<text, i64> = {\"a\": 17}
    var sum = 0
    sum = sum + nums.at(0).unwrap()
    if words.at(0).unwrap() == \"alpha\":
        sum = sum + 1
    if flags.at(0).unwrap():
        sum = sum + 2
    sum = sum + nums.at(9).unwrap_or(4)
    if nums.at(1).is_some():
        sum = sum + 8
    sum = sum + nums.get(2).unwrap_or(0)
    sum = sum + nums.min().unwrap_or(0)
    sum = sum + nums.max().unwrap_or(0)
    sum = sum + d.get(\"a\").unwrap_or(0)
    sum = sum + d.get(\"missing\").unwrap_or(5)
    sum
";
    assert!(parse_and_lower(valid_combined).is_ok(), "array and dict optional accessors should lower cleanly");
    assert_eq!(eval_source(valid_combined).expect("array and dict optional accessors eval"), 117);

    let individual_hir_and_eval_cases = [
        ("fn main() -> i64:\n    val xs: [i64] = [7]\n    xs.at(0).unwrap()\n", 7),
        ("fn main() -> i64:\n    val ws: [text] = [\"ok\"]\n    if ws.at(0).unwrap() == \"ok\": 1 else: 0\n", 1),
        ("fn main() -> i64:\n    val fs: [bool] = [true]\n    if fs.at(0).unwrap(): 1 else: 0\n", 1),
        ("fn main() -> i64:\n    val xs: [i64] = []\n    xs.at(0).unwrap_or(9)\n", 9),
        ("fn main() -> i64:\n    val xs: [i64] = [5]\n    if xs.at(0).is_some(): 1 else: 0\n", 1),
        ("fn main() -> i64:\n    val xs: [i64] = []\n    if xs.at(0).is_none(): 1 else: 0\n", 1),
        ("fn main() -> i64:\n    val xs: [i64] = [12]\n    xs.get(0).unwrap_or(0)\n", 12),
        ("fn main() -> i64:\n    val xs: [i64] = [4, 9]\n    xs.min().unwrap_or(0)\n", 4),
        ("fn main() -> i64:\n    val xs: [i64] = [4, 9]\n    xs.max().unwrap_or(0)\n", 9),
        ("fn main() -> i64:\n    val d: Dict<text, i64> = {\"k\": 21}\n    d.get(\"k\").unwrap_or(0)\n", 21),
    ];
    for (src, expected) in individual_hir_and_eval_cases {
        assert!(parse_and_lower(src).is_ok(), "expected HIR lowering ok for:\n{src}");
        assert_eq!(eval_source(src).expect("expected eval ok"), expected, "for:\n{src}");
    }

    let non_optional_cases = [
        "fn main() -> i64:\n    val x: i64 = 1\n    x.unwrap_or(0)\n",
        "fn main() -> i64:\n    val xs: [i64] = [1, 2]\n    xs.len().unwrap_or(0)\n",
        "fn main() -> i64:\n    val x: i64 = 1\n    match x:\n        case Some(v): v\n        case _: 0\n",
    ];
    for src in non_optional_cases {
        let hir_msg = lower_err(src);
        assert!(hir_msg.contains("SPL-PAT-001"), "unexpected HIR diagnostic `{hir_msg}` for:\n{src}");
        let eval_msg = eval_err(src);
        assert!(eval_msg.contains("SPL-PAT-001"), "unexpected eval diagnostic `{eval_msg}` for:\n{src}");
    }
}

#[test]
fn array_min_max_option_validation_does_not_route_to_rt_unwrap_or_trap() {
    use crate::hir::{HirExpr, HirExprKind, HirStmt};

    fn body_tail_expr<'a>(module: &'a crate::hir::HirModule, fn_name: &str) -> &'a HirExpr {
        let func = module
            .functions
            .iter()
            .find(|f| f.name == fn_name)
            .expect("function in lowered module");
        match func.body.last().expect("tail stmt") {
            HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => expr,
            other => panic!("unexpected tail stmt: {other:?}"),
        }
    }

    let no_trap_cases = [
        "fn probe() -> i64:\n    [3, 9].min().unwrap()\n",
        "fn probe() -> i64:\n    [3, 9].max().unwrap()\n",
        "fn probe() -> f64:\n    [1.5, 2.5].min().unwrap()\n",
        "fn probe() -> text:\n    [\"a\", \"b\"].max().unwrap()\n",
    ];
    for src in no_trap_cases {
        let module = parse_and_lower(src).expect("array min/max unwrap must lower without SPL-PAT-001");
        let tail = body_tail_expr(&module, "probe");
        assert!(
            !matches!(&tail.kind, HirExprKind::BuiltinCall { name, .. } if name == "rt_unwrap_or_trap"),
            "min/max unwrap must not lower to rt_unwrap_or_trap for:\n{src}\ngot: {tail:?}"
        );
    }

    let slot_trap_cases = [
        "fn probe() -> text:\n    [\"a\", \"b\"].first().unwrap()\n",
        "fn probe() -> f64:\n    var xs = [1.5, 2.5]\n    xs.pop().unwrap()\n",
    ];
    for src in slot_trap_cases {
        let module = parse_and_lower(src).expect("slot-yielding first/pop unwrap must lower cleanly");
        let tail = body_tail_expr(&module, "probe");
        assert!(
            matches!(&tail.kind, HirExprKind::BuiltinCall { name, .. } if name == "rt_unwrap_or_trap"),
            "slot-yielding first/pop unwrap must keep lowering to rt_unwrap_or_trap for:\n{src}\ngot: {tail:?}"
        );
    }

    assert!(parse_and_lower("fn probe() -> i64:\n    [3, 9].first().unwrap()\n").is_ok());
    assert!(parse_and_lower("fn probe() -> i64:\n    var xs = [3, 9]\n    xs.pop().unwrap()\n").is_ok());

    let valid_defaults = [
        ("fn main() -> i64:\n    [3, 9].min().unwrap_or(0)\n", 3),
        ("fn main() -> i64:\n    [3, 9].max().unwrap_or(0)\n", 9),
    ];
    for (src, expected) in valid_defaults {
        assert!(parse_and_lower(src).is_ok(), "min/max unwrap_or(0) should lower:\n{src}");
        assert_eq!(eval_source(src).expect("min/max unwrap_or(0) eval"), expected);
    }

    let mismatch = "fn main() -> i64:\n    [3, 9].min().unwrap_or(\"bad\")\n";
    let hir_msg = lower_err(mismatch);
    assert!(hir_msg.contains("SPL-PAT-001"), "unexpected HIR diagnostic `{hir_msg}`");
}
