# Escapes after a literal `{...}` group holding `\"` are kept undecoded

Status: open (P3, frontend lexer). Found 2026-11-28 on the Rust seed
`/home/yoon/.cache/cargo-target-wr-seed1126b/release/simple` while writing
AC-6 of `test/01_unit/browser_engine/css_rule_body_comment_chrome159_spec.spl`.

## Repro (whole literal; a minimal one is not found yet)

```
val SHEET: text = "body{margin:0;font:16px/1.5 sans-serif}.s{position:relative;width:400px;height:600px;overflow:hidden}\n#a{/* background-color:#d04060;width:40px;height:20px */}\n#b{height:10px;/* width:40px;height:20px */}\n#c{width:50px;/* width:40px;height:20px */ height:12px}\n/* #d{height:30px} */\n/* lead */ #e{height:14px}\n#f{height:16px}/* #f{height:31px;width:32px} */\n#g /* mid */ {height:18px}\n#h{width:/* x */60px;height:22px}\n#i{font-family:\"x/*y\";height:26px}\n#j{height:28px}/* c */\n#k{font-family:'a*/b/*';height:30px}\n#l{height:32px}\n#m{font-family:\"x\\\"/*y\";height:34px}\n#n{height:36px}/* c */\n#o{background:url(x/*a.png);height:38px}\n#p{height:40px}/* c2 */\n#q{font-family:\"x/*k\n;height:42px}\n#r{height:44px}/* z */ #s{height:46px}\n#t{content:\"\\\"\";height:48px}/* q */\n#u{height:50px}\n"
```

`print SHEET.substring(SHEET.index_of("#l"), SHEET.byte_len())` gives:

```
#l{height:32px}
#m{font-family:"x\"/*y";height:34px}\n#n{height:36px}/* c */\n#o{background:url(x/*a.png);height:38px}\n#p{height:40px}/* c2 */\n#q{font-family:"x/*k\n;height:42px}
#r{height:44px}/* z */ #s{height:46px}
```

From the `#m` group to the end of the `#q` group, every `\n` stays as the
two bytes `\` `n`. `W-STR-BRACE-001` is printed for the groups, and they
are kept as literal text as documented. The escapes are lost silently. The
`#m` and `#q` groups cut out alone into short strings decode correctly,
with or without `/*` and `/* c */` (tried 6 shapes). So the trigger needs
more of the context; the earlier `#i` (`"x/*y"`) or `#k` (`'a*/b/*'`)
groups are the next suspects.

## Expected

Escapes decode the same inside, between and after literal brace groups.

## Workaround in use

The spec writes `#m` and `#q` as `{{ ... }}` pieces joined with `+`.
