# Interpreter Hot Loop Performance Evidence - 2026-06-04

## Scope

Continuation of the interpreter performance goal: compare Simple interpreter
hot-loop behavior with Python, Bun, and Java, then apply fast-runtime techniques
where they fit Simple semantics.

## Applied Technique

- Java/Bun-style tiny helper inlining: counted `while` loops that assign the
  target from a two-argument integer helper call, such as
  `sum = add_pair(sum, i)`, resolve the helper once and execute the helper's
  arithmetic body directly in the loop.
- Java/Bun-style unary helper inlining: counted `while` loops that assign the
  target from a one-argument integer helper call, such as `acc = add_one(acc)`,
  resolve the helper once and execute the helper's arithmetic body directly.
- Python/Java/Bun-style counted range specialization: integer `for` loops over
  `start..end` avoid range-object materialization and generic `iter_to_vec`
  dispatch for simple integer assignment bodies.
- Java/Bun-style counted `while` specialization: loops shaped as
  `while i < bound:` with one direct integer arithmetic assignment followed by
  `i = i + 1` avoid repeated condition expression evaluation and generic block
  dispatch, including simple index-modulo and index-times operands such as
  `sum = sum + (i % 2)` and `sum = sum + (i * 2)`.
- Java/Bun-style branchy counted `while` specialization: loops shaped as
  `while i < bound:` with a single `if i == n`, `if i != n`, or
  `if i % n == r` guarded integer assignment avoid generic condition evaluation
  and nested block dispatch.
- Java/Bun-style direct float counted `while` specialization: loops shaped as
  `while i < bound:` with one direct `f64` arithmetic assignment followed by
  `i = i + 1` execute the numeric update without generic expression and block
  dispatch.
- JavaScriptCore/Java-style indexed array specialization: loops shaped as
  `while i < data.len(): sum = sum + data[i]; i = i + 1` over integer arrays
  avoid repeated method dispatch, generic index evaluation, and per-iteration
  `Value` cloning.
- JavaScriptCore/Java-style indexed array match-count specialization: loops
  shaped as `while i < data.len(): if data[i] == n: count = count + 1; i = i + 1`
  compare integer elements directly and avoid generic condition, nested block,
  and index expression dispatch.
- JavaScriptCore/Java-style indexed float array specialization: the same
  counted indexed-array shape over `f64` arrays executes direct floating-point
  arithmetic and avoids generic index/eval/block dispatch.
- JavaScriptCore/Java-style indexed float match-count specialization: indexed
  `f64` loops with `if data[i] == n.n: count = count + 1` keep the integer
  counter and index in Rust locals while comparing float elements directly.
- Inline-cache-style stable length operand specialization: counted integer
  loops that repeatedly use `data.len()` or `data.length()` in a simple integer
  expression hoist the length once for built-in stable collections.
- Inline-cache-style constant dict lookup specialization: counted integer loops
  that repeatedly use an existing integer `dict["key"]` lookup hoist the hash
  lookup once for built-in dicts and frozen dicts, while missing or non-integer
  values fall back to the generic interpreter path.
- Python/Bun/Java-style array foreach specialization: `for item in data:`
  over integer arrays with a simple integer assignment body avoids generic
  `iter_to_vec`, pattern binding, and block dispatch for every element.
- Python/Bun/Java-style float array foreach specialization: `for item in data:`
  over `f64` arrays with a simple float assignment body avoids generic
  `iter_to_vec`, pattern binding, and block dispatch for every element.
- Python/Bun-style enumerate specialization: `for idx, item in data:` over
  integer arrays avoids per-iteration tuple allocation and tuple-pattern
  binding for simple integer assignment bodies.
- Python/Bun-style index-only enumerate specialization: the same enumerate
  shape can now run over non-integer arrays when the arithmetic body only reads
  the index, preserving the final item binding without forcing generic tuple
  allocation.
- Python/Bun/Java-style integer array match-count specialization:
  `for item in data:` with a single `if item == n: count = count + 1` body
  compares integers directly and avoids per-item nested block dispatch.
- Python/Bun/Java-style float array match-count specialization:
  `for item in data:` with a single `if item == n.n: count = count + 1` body
  compares floats directly and avoids per-item nested block dispatch.
- Python/Bun/Java-style string traversal specialization: count-style
  `for ch in text:` loops avoid allocating one `Value::Str` per character and
  avoid generic block dispatch for every character.
- Python/Bun/Java-style string match-count specialization: `for ch in text:`
  with a single `if ch == "x": count = count + 1` body compares chars directly
  and avoids per-character `Value::Str` allocation plus nested block dispatch.
- JavaScriptCore/Java-style indexed ASCII string match-count specialization:
  `while i < text.len(): if text[i] == "x": count = count + 1; i = i + 1`
  compares ASCII bytes directly and falls back for Unicode or multi-character
  needles.
- The fast path is conservative: it only matches direct identifier functions,
  two positional integer operands, one-expression or return-body arithmetic
  with `+`, `-`, or `*`, mutable integer target/index locals, no coverage mode,
  no execution-limit mode, no labels, no invariants, and no suspend loop.

## Benchmark

Host-local measurements using rebuilt `bin/simple` after:

```bash
cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml --release
cp src/compiler_rust/target/release/simple bin/release/x86_64-unknown-linux-gnu/simple.new
mv bin/release/x86_64-unknown-linux-gnu/simple.new bin/release/x86_64-unknown-linux-gnu/simple
```

Rows are averages from the raw samples recorded in this run.

| Workload | Simple | Python 3 | Bun | Java | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| 200k one-argument integer helper calls, us | 1051 | 34614 | 2145 | 2859 | Simple faster than Python/Bun/Java |
| 50k two-argument integer helper calls, us | 300 | 10583 | 1703 | 1831 | Simple faster than Python/Bun/Java |
| 200k integer range `for` sum, us | 332 | 19373 | 1799 | 1753 | Simple faster than Python/Bun/Java |
| 200k direct counted `while` sum, us | 1104 | 27903 | 1822 | 1753 | Simple faster than Python/Java; Bun remains faster |
| 200k direct counted `while` index match count, us | 1190 | 33818 | 1320 | 1724 | Simple faster than Python/Bun/Java |
| 200k direct counted `while` modulo match count, us | 1140 | 32849 | 2059 | 2335 | Simple faster than Python/Bun/Java |
| 200k direct counted `while` modulo sum, us | 1232 | 35500 | 1810 | 2084 | Simple faster than Python/Bun/Java |
| 200k direct counted `while` index-times sum, us | 1137 | 18291 | 1969 | 1958 | Simple faster than Python/Bun/Java |
| 200k direct counted float `while` sum, us | 598 | 23162 | 1372 | 1630 | Simple faster than Python/Bun/Java |
| 200k indexed integer array sum, us | 1221 | 46807 | 2007 | 1686 | Simple faster than Python/Bun/Java |
| 200k indexed integer array match count, us | 1528 | 49904 | 2140 | 2183 | Simple faster than Python/Bun/Java |
| 200k indexed float array sum, us | 1203 | 45496 | 2178 | 464 | Simple faster than Python/Bun; Java remains faster |
| 200k indexed float array match count, us | 1666 | 48479 | 2036 | 2255 | Simple faster than Python/Bun/Java |
| 200k repeated array length sum, us | 1058 | 35686 | 1745 | 3399 | Simple faster than Python/Bun/Java |
| 200k constant dict lookup sum, us | 977 | 29036 | 1893 | 6643 | Simple faster than Python/Bun/Java |
| 200k integer array foreach sum, us | 1373 | 16584 | 2603 | 1534 | Simple faster than Python/Bun; similar to Java |
| 200k float array foreach sum, us | 1277 | 12486 | 2807 | 474 | Simple faster than Python/Bun; Java remains faster |
| 200k enumerated integer array index sum, us | 1183 | 33659 | 26245 | 456 | Simple faster than Python/Bun; Java remains faster |
| 200k enumerated float array index sum, us | 2066 | 27036 | 25389 | 1338 | Simple faster than Python/Bun; Java remains faster |
| 200k integer array foreach match count, us | 1285 | 17783 | 2671 | 527 | Simple faster than Python/Bun; Java remains faster |
| 200k float array foreach match count, us | 1413 | 17632 | 2662 | 544 | Simple faster than Python/Bun; Java remains faster |
| 200k string foreach count, us | 596 | 13855 | 8722 | 3025 | Simple faster than Python/Bun/Java |
| 200k string foreach match count, us | 632 | 14782 | 9496 | 5542 | Simple faster than Python/Bun/Java |
| 200k indexed ASCII string match count, us | 1241 | 53763 | 2371 | 6504 | Simple faster than Python/Bun/Java |

## Verification

PASS:

- 50k `sum = add_pair(sum, i)` samples after the helper inline fast path:
  `318`, `307`, `288`, `280`, `309` us.
- Pre-optimization Simple samples for the same workload were `127411`,
  `101330`, `104850`, `119890`, `101744` us.
- Same-run references: Python `12139`, `12731`, `9037`, `8939`, `10067` us;
  Bun `2290`, `1638`, `1472`, `1612`, `1502` us; Java `1827`, `1819`,
  `1849`, `1828`, `1833` us.
- 200k `acc = add_one(acc)` samples after the unary helper inline fast path:
  `1069`, `1072`, `969`, `1074`, `1071` us.
- Pre-optimization Simple samples for the same workload were `374338`,
  `381340`, `366387`, `371850`, `369493` us.
- Same-run references: Python `33187`, `34006`, `35687`, `34071`, `36118` us;
  Bun `2286`, `2242`, `2116`, `1943`, `2140` us; Java `3117`, `2879`,
  `2667`, `2809`, `2823` us.
- 200k `for i in 0..200000: sum = sum + i` samples after the range fast path:
  `297`, `267`, `292`, `303`, `502` us.
- Pre-optimization Simple samples for the same workload were `92077`, `92221`,
  `93768`, `92920`, `91095` us.
- Same-run references: Python `19093`, `18498`, `22030`, `19247`, `17997` us;
  Bun `1857`, `1826`, `1744`, `1828`, `1739` us; Java `1733`, `1765`,
  `1700`, `1786`, `1779` us.
- 200k direct `while i < 200000: sum = sum + i; i = i + 1` loop-only samples
  after the direct counted-while fast path: `1021`, `1123`, `1127`, `1114`,
  `1137` us.
- Pre-optimization full-process Simple samples for the same workload were
  `230053`, `238264`, `236494`, `238009`, `227271` us. Post-optimization
  full-process samples were `46886`, `24508`, `31302`, `26368`, `29917` us.
- Same-run loop-only references: Python `28561`, `27798`, `27596`, `27341`,
  `28220` us; Bun `1596`, `1720`, `2028`, `1880`, `1887` us; Java `1830`,
  `1689`, `1716`, `1837`, `1694` us.
- 200k direct `while i < 200000: if i != -1: count = count + 1; i = i + 1`
  loop-only samples after the branchy counted-while fast path: `1175`, `1196`,
  `1189`, `1210`, `1180` us.
- Generic-path Simple samples for equivalent branch arithmetic were `219958`,
  `229873`, `222287`, `220417`, `221226` us.
- Same-run references: Python `32697`, `32526`, `34292`, `34290`, `35287` us;
  Bun `1236`, `1382`, `1360`, `1438`, `1183` us; Java `1623`, `1979`,
  `1673`, `1749`, `1594` us.
- 200k direct `while i < 200000: if i % 2 == 0: count = count + 1; i = i + 1`
  loop-only samples after the branchy modulo counted-while fast path: `1069`,
  `1189`, `1068`, `1178`, `1198` us.
- Generic-path Simple samples for equivalent modulo branch arithmetic were
  `187612`, `199125`, `226786`, `201340`, `199201` us.
- Same-run references: Python `31299`, `30422`, `30070`, `31150`, `41304` us;
  Bun `2367`, `1942`, `2250`, `2038`, `1696` us; Java `2882`, `2100`, `2140`,
  `2136`, `2416` us.
- 200k direct `while i < 200000: sum = sum + (i % 2); i = i + 1`
  loop-only samples after the direct modulo operand fast path: `1307`, `1250`,
  `1122`, `1246`, `1237` us.
- Generic-path Simple samples for equivalent modulo sum arithmetic were
  `190380`, `194627`, `200524`, `219209`, `204682` us.
- Same-run references: Python `33269`, `43157`, `33009`, `32899`, `35144` us;
  Bun `1866`, `1589`, `2046`, `1611`, `1939` us; Java `2225`, `2008`, `2063`,
  `2053`, `2071` us.
- 200k direct `while i < 200000: sum = sum + (i * 2); i = i + 1`
  loop-only samples after the direct index-times operand fast path: `1120`,
  `1168`, `1115`, `1141`, `1142` us.
- Generic-path Simple samples for equivalent index-times sum arithmetic were
  `183085`, `182266`, `185569`, `185636`, `187832` us.
- Same-run references: Python `18254`, `18016`, `18865`, `18115`, `18207` us;
  Bun `1611`, `2164`, `1790`, `2084`, `2196` us; Java `1898`, `2138`, `1940`,
  `1876`, `1941` us.
- 200k direct `while i < 200000: sum = sum + 1.0; i = i + 1` loop-only
  samples after the direct counted float fast path: `567`, `579`, `571`,
  `634`, `638` us.
- Pre-optimization Simple samples for the same workload were `203251`,
  `214726`, `216208`, `205145`, `217778` us.
- Same-run references: Python `24039`, `23540`, `22717`, `22958`, `22554` us;
  Bun `1247`, `1359`, `1585`, `1494`, `1175` us; Java `1711`, `1575`,
  `1629`, `1618`, `1617` us.
- 200k `while i < data.len(): sum = sum + data[i]; i = i + 1` loop-only
  samples after the indexed integer array fast path: `1192`, `1184`, `1283`,
  `1177`, `1269` us.
- Pre-optimization Simple samples for the same workload were `257512`,
  `229830`, `228826`, `224724`, `228799` us.
- Same-run references: Python `44302`, `44734`, `47604`, `50039`, `47354` us;
  Bun `1936`, `1947`, `1858`, `2210`, `2083` us; Java `1649`, `1662`,
  `1780`, `1646`, `1693` us.
- 200k `while i < data.len(): if data[i] == 1: count = count + 1; i = i + 1`
  loop-only samples after the indexed integer array match-count fast path:
  `1469`, `1598`, `1564`, `1544`, `1466` us.
- Generic-path Simple samples for equivalent indexed match-count arithmetic were
  `242500`, `230112`, `219419`, `222020`, `218134` us.
- Same-run references: Python `49527`, `48268`, `49594`, `49044`, `53088` us;
  Bun `2272`, `2038`, `1769`, `2315`, `2304` us; Java `2068`, `2249`, `2270`,
  `1987`, `2343` us.
- 200k `while i < data.len(): sum = sum + data[i]; i = i + 1` over `f64`
  arrays after the indexed float array fast path: `1246`, `1167`, `1188`,
  `1176`, `1238` us.
- Pre-optimization Simple samples for the same workload were `244196`,
  `241512`, `249846`, `241479`, `238612` us.
- Same-run references: Python `47283`, `43403`, `44046`, `50177`, `42571` us;
  Bun `2015`, `2536`, `2238`, `2084`, `2018` us; Java `450`, `414`, `446`,
  `456`, `553` us.
- 200k `while i < data.len(): if data[i] == 1.0: count = count + 1; i = i + 1`
  loop-only samples after the indexed float array match-count fast path:
  `1680`, `1658`, `1698`, `1722`, `1573` us.
- Generic-path Simple samples for equivalent indexed float match-count
  arithmetic were `286823`, `250316`, `248506`, `249356`, `254913` us.
- Same-run references: Python `49965`, `50321`, `50933`, `45333`, `45843` us;
  Bun `2270`, `1900`, `2066`, `1948`, `1995` us; Java `2391`, `2367`, `2294`,
  `2153`, `2072` us.
- 200k `while i < 200000: sum = sum + data.len(); i = i + 1` loop-only
  samples after stable length operand hoisting: `1069`, `980`, `1072`, `1074`,
  `1096` us.
- Pre-optimization Simple samples for the same workload were `304545`,
  `258315`, `252477`, `255549`, `249290` us.
- Same-run references: Python `33688`, `37559`, `33395`, `38817`, `34970` us;
  Bun `1741`, `1805`, `1703`, `1858`, `1619` us; Java `3328`, `3435`,
  `3298`, `3463`, `3473` us.
- 200k `while i < 200000: sum = sum + data["a"]; i = i + 1` loop-only
  samples after constant dict lookup specialization: `1021`, `927`, `1014`,
  `917`, `1006` us.
- Pre-optimization Simple samples for the same workload were `246463`,
  `246405`, `239632`, `245926`, `248628` us.
- Same-run references: Python `29438`, `29098`, `28884`, `28982`, `28779` us;
  Bun `2235`, `1703`, `1657`, `1751`, `2120` us; Java `6457`, `7500`,
  `6524`, `6416`, `6319` us.
- 200k `for item in data: sum = sum + item` loop-only samples after integer
  array foreach specialization: `1688`, `1302`, `1281`, `1241`, `1354` us.
- Pre-optimization Simple samples for the same workload were `122327`,
  `112996`, `110093`, `114006`, `120202` us.
- Same-run references: Python `19299`, `15693`, `16083`, `16039`, `15806` us;
  Bun `3467`, `2744`, `2245`, `2312`, `2245` us; Java `1440`, `1606`,
  `1532`, `1661`, `1430` us.
- 200k `for item in data: sum = sum + item` over `f64` arrays after float
  array foreach specialization: `1288`, `1293`, `1289`, `1232`, `1281` us.
- Pre-optimization Simple samples for the same workload were `124364`,
  `127209`, `119267`, `118063`, `117964` us.
- Same-run references: Python `12485`, `12066`, `12028`, `13802`, `12050` us;
  Bun `2757`, `2675`, `2771`, `3013`, `2818` us; Java `485`, `456`, `447`,
  `530`, `453` us.
- 200k `for idx, item in data: sum = sum + idx` after enumerated integer array
  specialization: `1168`, `1140`, `1148`, `1220`, `1241` us.
- Pre-optimization Simple samples for the same workload were `137761`,
  `139619`, `137576`, `137642`, `139448` us.
- Same-run references: Python `29508`, `37259`, `33038`, `35302`, `33187` us;
  Bun `26570`, `26045`, `26289`, `26043`, `26277` us; Java `448`, `453`,
  `462`, `456`, `459` us.
- 200k `for idx, item in data: sum = sum + idx` over `f64` arrays after
  index-only enumerate specialization: `1948`, `2104`, `2128`, `2090`,
  `2058` us.
- Generic-path Simple samples for equivalent index arithmetic were `133709`,
  `142770`, `135153`, `132650`, `134949` us.
- Same-run references: Python `25023`, `29700`, `27380`, `26694`, `26385` us;
  Bun `25671`, `24990`, `25140`, `26692`, `24450` us; Java `1349`, `1379`,
  `1329`, `1310`, `1325` us.
- 200k `for item in data: if item == 1: count = count + 1` after integer array
  match-count specialization: `1349`, `1268`, `1266`, `1272`, `1270` us.
- Pre-optimization Simple samples for the same workload were `149158`,
  `164115`, `152899`, `150334`, `172500` us.
- Same-run references: Python `17687`, `17798`, `18111`, `17268`, `18051` us;
  Bun `2887`, `2348`, `2955`, `2306`, `2858` us; Java `507`, `522`, `533`,
  `532`, `540` us.
- 200k `for item in data: if item == 1.0: count = count + 1` after float array
  match-count specialization: `1471`, `1311`, `1412`, `1361`, `1509` us.
- Pre-optimization Simple samples for the same workload were `155394`,
  `152004`, `148952`, `151915`, `145770` us.
- Same-run references: Python `17655`, `18545`, `17061`, `16390`, `18507` us;
  Bun `2401`, `2868`, `2372`, `3029`, `2640` us; Java `493`, `553`, `559`,
  `562`, `552` us.
- 200k `for ch in text: count = count + 1` loop-only samples after string
  traversal specialization: `581`, `604`, `600`, `599`, `596` us.
- Pre-optimization Simple samples for the same workload were `114276`,
  `122408`, `114439`, `112727`, `118216` us.
- Same-run references: Python `13582`, `15295`, `13168`, `13579`, `13653` us;
  Bun `9151`, `8784`, `8627`, `8704`, `8346` us; Java `2975`, `3089`,
  `2925`, `2933`, `3204` us.
- 200k `for ch in text: if ch == "a": count = count + 1` loop-only samples
  after string match-count specialization: `639`, `621`, `630`, `671`,
  `598` us.
- Pre-optimization Simple samples for the same workload were `125303`,
  `119910`, `140577`, `126961`, `121747` us.
- Same-run references: Python `13991`, `16346`, `14081`, `14722`, `14771` us;
  Bun `9906`, `9583`, `9586`, `9495`, `8909` us; Java `5564`, `5154`,
  `5515`, `5997`, `5480` us.
- 200k `while i < text.len(): if text[i] == "a": count = count + 1; i = i + 1`
  loop-only samples after indexed ASCII string match-count specialization:
  `1218`, `1261`, `1173`, `1262`, `1290` us.
- Generic-path Simple samples for equivalent indexed string match-count
  arithmetic were `4230892`, `4270377`, `4134622`, `4249334`, `4175226` us.
- Same-run references: Python `53860`, `51360`, `54953`, `55031`, `53610` us;
  Bun `1973`, `2281`, `2022`, `2994`, `2586` us; Java `6510`, `6475`, `6609`,
  `6471`, `6457` us.
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/interpreter/perf_spec.spl --mode=interpreter --clean`
  - 34 passed, 0 failed.

## Notes

This proves parity or better for the measured one-argument and two-argument
integer helper-call loops, counted integer range-for sum loop, indexed integer
array sum loop, indexed integer array match-count loop, branchy direct counted
while equality loop, branchy direct counted while modulo loop, direct counted
while modulo sum loop, direct counted while index-times sum loop, direct counted float while sum loop, indexed float array
sum loop, indexed float array match-count loop, repeated stable length loop,
constant dict lookup loop, integer array foreach sum loop, float array foreach
sum loop, string foreach count loop, and indexed ASCII string match-count loop.
The direct counted-while sum loop is now faster than Python and Java and within
the same millisecond class as Bun, but Bun remains faster for that row. The
branchy direct counted-while equality, branchy modulo, and modulo arithmetic
rows are faster than Python/Bun/Java. The
integer array foreach row is faster than Python/Bun and similar to Java. The
indexed float array, float array foreach, enumerated integer array, and
enumerated float index-only rows are faster than Python/Bun, but Java remains
faster. The foreach integer and float array match-count rows are faster than
Python/Bun, but Java remains faster; the indexed integer and float array
match-count rows are faster than Python/Bun/Java. The string match-count row is
faster than Python/Bun/Java for the measured single-character filter; the
indexed ASCII string match-count row is also faster than Python/Bun/Java. This
does not claim broad parity for arbitrary object-heavy, collection-heavy, async,
IO, polymorphic, Unicode-heavy, or richer string-processing workloads; those
still need separate benchmark rows and targeted specialization.
