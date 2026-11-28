# rt-scan.awk: shared scanner for the rt_ map gates (POSIX awk; no gawk-only features).
#
# One awk program behind check-rt-host-map.shs, check-rt-pointer-ref-map.shs,
# rt-binding-index.shs and check-rt-c-contract-compile.shs. It replaces the four
# Python originals. Selected by `-v MODE=host|ptr|index|contract`.
#
# Environment (never -v, so backslashes in paths are not escape-processed):
#   RT_ROOT     tree root, no trailing slash ("" only for the in-memory selftests)
#   RT_OUT      rt-binding-index --out path ("" = stdout)
#   RT_CC       compiler command line (contract), RT_TMP scratch dir, RT_TUS newline list
#   RT_TIMEOUT  "timeout 300" or "" (prefix for compiler runs)
#   RT_UNAME    `uname -sm` (contract host line), RT_SELF  repo root for the contract selftest
# File list: one path per line on stdin (find output, ROOT-prefixed).
# Flags (-v): SELFTEST REGEN REGEN_PARAM INCSELF (host include selftest, real tree)
#
# Deliberate deviations from the Python originals (all documented, none silent):
#  1. Python regex features without an awk equivalent (lookahead, lazy quantifiers,
#     DOTALL, \b) are re-expressed as explicit scanners or equivalent POSIX EREs.
#     Where an ERE only has to answer "does a match exist" (NULLRET, ENFORCED) the
#     answer is identical; where the original returns captured text a scanner is used.
#  2. Files are read line by line. A trailing CR is stripped from each line (Python
#     translated CRLF); a lone CR inside a line is NOT treated as a line break.
#  3. Quoted-include ownership: a child is owned only if `find src/runtime -type f`
#     listed it (regular files, no symlinks), after LEXICAL normalisation of ".."/".".
#     This is slightly stricter than realpath-inside-runtime: a path that reaches a
#     regular file through a directory symlink is not followed.
#  4. File scans use the same `find -type f` list: a symlinked .c/.spl/.rs file that
#     os.walk would have opened is not read (fail-closed: fewer providers, never more).
#  5. Rust `extern "C" fn rt_x` is matched within a window of the line holding
#     `extern` and the next 3 lines (Python joined the whole file); a declaration
#     split over more than 4 lines is missed.
#  6. `extern fn rt_x<...>` generics must be on one line; a multi-line `<...>` skips
#     the record. Parameter lists may span lines.
#  7. Non-ASCII bytes in a rt-binding-index string value are a hard ERROR (exit 2)
#     instead of \uXXXX escaping; the real tree has none.
#  8. The interface id is sha256 computed in-process (portable awk) instead of one
#     sha256sum spawn per record (thousands of spawns); verified equal to sha256sum.
#  9. rt-binding-index/contract paths always use "/" (Python on Windows printed "\").
# 10. Contract TU text-ABI table errors, which crashed Python with a traceback, are
#     reported as `ERROR — <message>` exit 2.
# 11. A backslash-newline inside a string literal that is not terminated is handled
#     like Python only for the common terminated case.
#
# Tri-state truth: 1 true, 0 false, -1 unknown (None).

function trim(s) { sub(/^[[:space:]]+/, "", s); sub(/[[:space:]]+$/, "", s); return s }
function norm_ws(s) { gsub(/[[:space:]]+/, " ", s); return trim(s) }
function endsw(s, e) { return length(s) >= length(e) && substr(s, length(s) - length(e) + 1) == e }
function startsw(s, p) { return substr(s, 1, length(p)) == p }
function isabs(n) { return n ~ /^[\/\\]/ || n ~ /^[A-Za-z]:/ }
function q(s) { gsub(/'/, "'\\''", s); return "'" s "'" }

# whole word `w` occurs in s (word = [A-Za-z0-9_] run)
function has_word(s, w,    off, rest, p, b, a) {
  off = 0; rest = s
  while ((p = index(rest, w)) > 0) {
    b = (off + p > 1) ? substr(s, off + p - 1, 1) : ""
    a = substr(s, off + p + length(w), 1)
    if (b !~ /[A-Za-z0-9_]/ && a !~ /[A-Za-z0-9_]/) return 1
    off += p; rest = substr(s, off + 1)
  }
  return 0
}

# bytewise ascending merge sort of a[1..n] (strings)
function msort(a, n,    w, width, i, lo, mid, hi, p, qq, k) {
  for (width = 1; width < n; width *= 2) {
    for (lo = 1; lo <= n; lo += 2 * width) {
      mid = lo + width; hi = lo + 2 * width
      if (mid > n + 1) mid = n + 1
      if (hi > n + 1) hi = n + 1
      p = lo; qq = mid; k = lo
      while (p < mid && qq < hi) {
        if ((a[qq] "") < (a[p] "")) w[k++] = a[qq++]; else w[k++] = a[p++]
      }
      while (p < mid) w[k++] = a[p++]
      while (qq < hi) w[k++] = a[qq++]
    }
    for (i = 1; i <= n; i++) a[i] = w[i]
  }
}
function keys_sorted(S, out,    k, n) { split("", out); n = 0; for (k in S) out[++n] = k; msort(out, n); return n }
function set_count(S,    k, n) { n = 0; for (k in S) n++; return n }

# ---------------------------------------------------------------- file system layer
function vf_reset() { VIRT = 1; ROOT = ""; split("", VF); split("", FL); split("", FSET); FN = 0 }
function vf_put(rel, content) { VF[rel] = content; if (!(rel in FSET)) { FL[++FN] = rel; FSET[rel] = 1 } }
function fs_list_load(    line, n, pre) {
  FN = 0; split("", FL); split("", FSET)
  pre = ROOT "/"
  while ((getline line < "-") > 0) {
    sub(/\r$/, "", line)
    if (line == "") continue
    if (substr(line, 1, length(pre)) == pre) line = substr(line, length(pre) + 1)
    if (!(line in FSET)) { FL[++FN] = line; FSET[line] = 1 }
  }
}
function fs_path(rel) { return (isabs(rel) || ROOT == "") ? rel : ROOT "/" rel }
function fs_read(rel, arr,    n, line, p, rc) {
  split("", arr); n = 0
  if (VIRT) {
    if (!(rel in VF)) return -1
    n = split(VF[rel], arr, "\n")
    if (n > 0 && arr[n] == "") n--
    return n
  }
  p = fs_path(rel)
  rc = (getline line < p)
  if (rc < 0) return -1
  while (rc > 0) { sub(/\r$/, "", line); arr[++n] = line; rc = (getline line < p) }
  close(p)
  return n
}
function fs_write(rel, text,    p) {
  if (VIRT) { VF[rel] = text; return }
  p = fs_path(rel)
  printf "%s", text > p
  close(p)
}
# rel path lies under top/ with no intermediate directory named in excl (" a b ")
function under(rel, top, excl,    rest, n, parts, i) {
  if (substr(rel, 1, length(top) + 1) != top "/") return 0
  rest = substr(rel, length(top) + 2)
  n = split(rest, parts, "/")
  for (i = 1; i < n; i++) if (index(excl, " " parts[i] " ")) return 0
  return 1
}
function in_spl_tops(rel, excl,    t) {
  if (!endsw(rel, ".spl")) return 0
  for (t = 1; t <= 4; t++) if (under(rel, TOPS[t], excl)) return 1
  return 0
}

# ---------------------------------------------------------------- C text normalisation
# kstr: keep "..." literals verbatim, else blank them; chr: treat '...' literals as noise;
# keepnl: a comment becomes " " plus its newlines (else a single " "). Returns the text.
function strip_c(L, n, kstr, chr, keepnl,    ln, buf, out, i, rem, k, s0, c, c2, p, cm, nl, j, ch, ok, qq) {
  out = ""
  for (ln = 1; ln <= n; ln++) {
    buf = L[ln]; i = 1
    while (1) {
      rem = substr(buf, i)
      if (chr) k = match(rem, /[\/"']/); else k = match(rem, /[\/"]/)
      if (!k) { out = out rem; break }
      s0 = RSTART
      out = out substr(rem, 1, s0 - 1)
      i += s0 - 1
      c = substr(buf, i, 1)
      if (c == "/") {
        c2 = substr(buf, i + 1, 1)
        if (c2 == "*") {
          p = index(substr(buf, i + 2), "*/")
          while (!p && ln < n) {
            ln++
            if (index(L[ln], "*/")) { buf = buf "\n" L[ln]; p = index(substr(buf, i + 2), "*/"); break }
            buf = buf "\n" L[ln]
          }
          if (p) {
            cm = substr(buf, i, p + 3)
            out = out " "
            if (keepnl) { nl = gsub(/\n/, "\n", cm); while (nl-- > 0) out = out "\n" }
            i += p + 3
            continue
          }
          out = out "/"; i++; continue
        }
        if (c2 == "/") {
          p = index(substr(buf, i), "\n")
          out = out " "
          if (p) i += p - 1; else i = length(buf) + 1
          continue
        }
        out = out "/"; i++; continue
      }
      qq = c; j = i + 1; ok = 0
      while (1) {
        ch = substr(buf, j, 1)
        if (ch == "") break
        if (ch == "\\") {
          if (j + 1 <= length(buf)) { j += 2; continue }
          if (ln < n) { ln++; buf = buf "\n" L[ln]; j += 2; continue }
          break
        }
        if (ch == qq) { ok = 1; break }
        if (ch == "\n") break
        j++
      }
      if (ok) {
        if (kstr && qq == "\"") out = out substr(buf, i, j - i + 1); else out = out " "
        i = j + 1
      } else { out = out c; i++ }
    }
    out = out "\n"
  }
  return out
}

# __attribute__((...)) removal; trail=1 also eats following blanks (pointer map ATTR)
function strip_attr(s, repl, trail,    out, p, rest, k, j, len, c, t, ok, endpos, cons) {
  if (!index(s, "__attribute__")) return s
  out = ""
  while ((p = index(s, "__attribute__")) > 0) {
    out = out substr(s, 1, p - 1)
    rest = substr(s, p + 13)
    ok = 0
    if (match(rest, /^[[:space:]]*\(\(/)) {
      k = RLENGTH; j = k + 1; len = length(rest)
      while (j <= len) {
        c = substr(rest, j, 1)
        if (c == "(") {
          t = j + 1
          while (t <= len && substr(rest, t, 1) !~ /[()]/) t++
          if (t <= len && substr(rest, t, 1) == ")") { j = t + 1; continue }
          break
        } else if (c == ")") {
          if (substr(rest, j + 1, 1) == ")") { ok = 1; endpos = j + 1 }
          break
        } else j++
      }
    }
    if (ok) {
      cons = 13 + endpos
      if (trail) { match(substr(s, p + cons), /^[ \t]*/); cons += RLENGTH }
      out = out repl
      s = substr(s, p + cons)
    } else {
      out = out "__attribute__"
      s = substr(s, p + 13)
    }
  }
  return out s
}

# C_STRING.sub(' ', line): blank "..." literals on one line
function blank_str(s,    out, k, j, ch, ok, n) {
  if (index(s, "\"") == 0) return s
  out = ""
  while ((k = index(s, "\"")) > 0) {
    out = out substr(s, 1, k - 1)
    j = k + 1; ok = 0; n = length(s)
    while (j <= n) {
      ch = substr(s, j, 1)
      if (ch == "\\") { if (j < n) { j += 2; continue } break }
      if (ch == "\"") { ok = 1; break }
      j++
    }
    if (ok) { out = out " "; s = substr(s, j + 1) } else { out = out "\""; s = substr(s, k + 1) }
  }
  return out s
}

# ---------------------------------------------------------------- tri-state #if evaluation
function n3(a) { return (a == -1) ? -1 : 1 - a }
function a3(a, b) { if (a == 0 || b == 0) return 0; if (a == -1 || b == -1) return -1; return 1 }
function o3(a, b) { if (a == 1 || b == 1) return 1; if (a == -1 || b == -1) return -1; return 0 }

function tokenize(e,    p, i, n, rest, c, two) {
  p = index(e, "//"); if (p) e = substr(e, 1, p - 1)
  p = index(e, "/*"); if (p) e = substr(e, 1, p - 1)
  TN = 0; i = 1; n = length(e)
  while (i <= n) {
    while (i <= n && substr(e, i, 1) ~ /[[:space:]]/) i++
    if (i > n) break
    rest = substr(e, i)
    if (substr(rest, 1, 7) == "defined") {
      if (match(rest, /^defined[[:space:]]*\([[:space:]]*[A-Za-z0-9_]+[[:space:]]*\)/) || \
          match(rest, /^defined[[:space:]]+[A-Za-z0-9_]+/)) {
        TK[++TN] = substr(rest, 1, RLENGTH); i += RLENGTH; continue
      }
    }
    c = substr(rest, 1, 1); two = substr(rest, 1, 2)
    if (two == "&&" || two == "||") { TK[++TN] = two; i += 2; continue }
    if (c == "!" || c == "(" || c == ")") { TK[++TN] = c; i++; continue }
    if (c == "&" || c == "|") { i++; continue }
    match(rest, /^[^[:space:]()&|!]+/)
    TK[++TN] = substr(rest, 1, RLENGTH); i += RLENGTH
  }
}
function p_prim(    t, has, v, m) {
  has = (PI <= TN); t = has ? TK[PI] : ""; PI++
  if (has && t == "!") return n3(p_prim())
  if (has && t == "(") {
    v = p_or()
    if (!(PI <= TN && TK[PI] == ")")) { PERR = 1; return -1 }
    PI++; return v
  }
  if (has && substr(t, 1, 7) == "defined") {
    m = t; sub(/[^A-Za-z0-9_]+$/, "", m); match(m, /[A-Za-z0-9_]+$/); m = substr(m, RSTART)
    if (m in KNOWN) return ((H SUBSEP m) in HM) ? 1 : 0
    return -1
  }
  if (has && t ~ /^[0-9]+$/) return (t != "0") ? 1 : 0
  if (has && (t in KNOWN)) return ((H SUBSEP t) in HM) ? 1 : 0
  return -1
}
function p_and(    v) { v = p_prim(); while (PI <= TN && TK[PI] == "&&") { PI++; v = a3(v, p_prim()) } return v }
function p_or(    v) { v = p_and(); while (PI <= TN && TK[PI] == "||") { PI++; v = o3(v, p_and()) } return v }
function evaluate(e, host,    v) {
  H = host; tokenize(e); PI = 1; PERR = 0
  v = p_or()
  if (PERR) return -1
  return (PI == TN + 1) ? v : -1
}

# directive parse: DKIND "" when the line is not an if-family directive
function dir_parse(line,    w) {
  DKIND = ""; DREST = ""
  if (!match(line, /^[[:space:]]*#[[:space:]]*[A-Za-z0-9_]+/)) return
  w = substr(line, RSTART, RLENGTH); sub(/^[[:space:]]*#[[:space:]]*/, "", w)
  if (w !~ /^(ifdef|ifndef|if|elif|else|endif)$/) return
  DKIND = w
  DREST = trim(substr(line, RSTART + RLENGTH))
}

# ---------------------------------------------------------------- host map
function file_host(rel,    p, s, n, toks, i) {
  if (index(rel, "startup/baremetal/")) return "simpleos"
  p = index(rel, "src/runtime")
  s = (p ? substr(rel, p + 11) : rel)
  gsub(/[-_.\/\\]/, " ", s)
  n = split(s, toks, " ")
  for (i = 1; i <= n; i++) if (toks[i] in SUFFIX) return SUFFIX[toks[i]]
  return ""
}
function hc_id(rel,    id, n, i, lines, txt, RL2) {
  if (rel in FID) return FID[rel]
  id = ++FIDN; FID[rel] = id
  FREL[id] = rel
  n = fs_read(rel, HRL)
  HASATTR[id] = 0
  for (i = 1; i <= n; i++) if (index(HRL[i], "__attribute__")) { HASATTR[id] = 1; break }
  txt = strip_c(HRL, n, 1, 0, 1)
  gsub(/\\\n/, " ", txt)
  n = split(txt, lines, "\n")
  if (n > 0 && lines[n] == "") n--
  CN[id] = n
  for (i = 1; i <= n; i++) { CL[id, i] = lines[i]; dir_parse(lines[i]); DK[id, i] = DKIND; DR[id, i] = DREST }
  return id
}
# fills V[1..n] with the host view of file id f
function host_view(f, host, definite,    n, i, line, k, rest, nm, v, a, sp, j, bad) {
  sp = 0; n = CN[f]
  for (i = 1; i <= n; i++) {
    k = DK[f, i]
    if (k != "") {
      rest = DR[f, i]
      if (k == "ifdef" || k == "ifndef") {
        nm = rest; sub(/[[:space:]].*$/, "", nm)
        if (nm in KNOWN) v = ((host SUBSEP nm) in HM) ? 1 : 0; else v = -1
        a = (k == "ifdef") ? v : n3(v)
        sp++; ACT[sp] = a; TAK[sp] = a
      } else if (k == "if") {
        v = evaluate(rest, host); sp++; ACT[sp] = v; TAK[sp] = v
      } else if (sp > 0 && k == "elif") {
        v = a3(n3(TAK[sp]), evaluate(rest, host)); TAK[sp] = o3(TAK[sp], v); ACT[sp] = v
      } else if (sp > 0 && k == "else") {
        ACT[sp] = n3(TAK[sp]); TAK[sp] = 1
      } else if (sp > 0) sp--
      V[i] = ""
    } else {
      bad = 0
      for (j = 1; j <= sp; j++) {
        if (ACT[j] == 0) { bad = 1; break }
        if (definite && ACT[j] != 1) { bad = 1; break }
      }
      V[i] = bad ? "" : CL[f, i]
    }
  }
  return n
}
# external definition name of one `{`-terminated declaration segment, or ""
function def_name(decl,    k, d, j, line, R, Rt, T, restt, p, pre, rl) {
  if (index(decl, "rt_") == 0) return ""
  k = split(decl, d, "\n")
  for (j = 1; j <= k; j++) {
    line = d[j]
    match(line, /^[A-Za-z0-9_ \t*]*/); rl = RLENGTH
    R = substr(line, 1, rl)
    if (substr(line, rl + 1, 1) != "(") continue
    Rt = R; sub(/[ \t]+$/, "", Rt)
    if (!match(Rt, /[A-Za-z0-9_]+$/)) continue
    T = substr(Rt, RSTART)
    if (T !~ /^rt_[A-Za-z0-9_]+$/) continue
    if (has_word(R, "static")) continue
    restt = substr(line, rl + 1)
    for (p = j + 1; p <= k; p++) restt = restt "\n" d[p]
    sub(/[[:space:]]+$/, "", restt)
    if (length(restt) < 2 || substr(restt, length(restt), 1) != ")") continue
    pre = ""
    for (p = 1; p < j; p++) pre = pre d[p] "\n"
    pre = pre Rt
    if (has_word(pre, "static")) return ""
    return T
  }
  return ""
}
function provider_defs(W, n, tgt, pfx,    i, t, decl, k, ch, nm) {
  decl = ""
  for (i = 1; i <= n; i++) {
    t = W[i]
    if (t ~ /^[ \t]*#/) t = ""
    while (match(t, /[;{}]/)) {
      k = RSTART; ch = substr(t, k, 1)
      decl = decl substr(t, 1, k - 1)
      if (ch == "{") { nm = def_name(decl); if (nm != "") tgt[pfx nm] = 1 }
      decl = ""
      t = substr(t, k + 1)
    }
    decl = decl t "\n"
  }
}
function norm_path(p,    n, parts, i, out, m) {
  n = split(p, parts, "/"); m = 0
  for (i = 1; i <= n; i++) {
    if (parts[i] == "" || parts[i] == ".") continue
    if (parts[i] == "..") { if (m == 0) return ""; m--; continue }
    OUTP[++m] = parts[i]
  }
  out = ""
  for (i = 1; i <= m; i++) out = out (i > 1 ? "/" : "") OUTP[i]
  return out
}
function owned_rel(rel,    n, parts, i, sub_) {
  if (!(rel in FSET)) return 0
  if (substr(rel, 1, 12) != "src/runtime/") return 0
  sub_ = substr(rel, 13)
  n = split(sub_, parts, "/")
  for (i = 1; i <= n; i++) if (parts[i] == "vendor" || parts[i] == "test" || parts[i] == "target") return 0
  if (sub_ == "miniaudio.h" || sub_ == "stb_image.h" || sub_ == "stb_truetype.h") return 0
  return 1
}
function host_pass(h, definite,    sp, f, n, i, line, s, qi, name, dir, child, W, wn, txt, pfx, tgt, a, m, pos) {
  split("", SEEN); sp = 0
  for (i = 1; i <= RTN; i++) if (RTHOST[i] == "" || RTHOST[i] == h) PEND[++sp] = RTID[i]
  pfx = h ":"
  while (sp > 0) {
    f = PEND[sp--]
    if (f in SEEN) continue
    SEEN[f] = 1; VISIT[h, definite, f]++
    n = host_view(f, h, definite)
    for (i = 1; i <= n; i++) {
      line = V[i]
      if (index(line, "include") && match(line, /^[ \t]*#[ \t]*include[ \t]*"[^"]+"/)) {
        s = substr(line, RSTART, RLENGTH); qi = index(s, "\"")
        name = substr(s, qi + 1, length(s) - qi - 1)
        if (isabs(name)) continue
        dir = FREL[f]; sub(/[^\/]*$/, "", dir)
        child = norm_path(dir name)
        if (child != "" && owned_rel(child)) PEND[++sp] = hc_id(child)
      }
    }
    wn = 0
    for (i = 1; i <= n; i++) W[++wn] = blank_str(V[i])
    if (HASATTR[f]) {
      txt = ""
      for (i = 1; i <= wn; i++) txt = txt W[i] "\n"
      txt = strip_attr(txt, " ", 0)
      wn = split(txt, W, "\n"); if (wn > 0 && W[wn] == "") wn--
    }
    if (definite) provider_defs(W, wn, DEFN, pfx); else provider_defs(W, wn, PROV, pfx)
  }
}
function scan_rs(rel,    n, i, w, m) {
  n = fs_read(rel, RSL)
  for (i = 1; i <= n; i++) {
    if (!index(RSL[i], "extern")) continue
    w = RSL[i] " " RSL[i + 1] " " RSL[i + 2] " " RSL[i + 3]
    while (match(w, /extern[[:space:]]+"C"[[:space:]]+fn[[:space:]]+rt_[A-Za-z0-9_]+/)) {
      m = substr(w, RSTART, RLENGTH); w = substr(w, RSTART + RLENGTH)
      match(m, /rt_[A-Za-z0-9_]+$/); RUSTS[substr(m, RSTART)] = 1
    }
  }
}
function scan_decl_simple(rel,    n, i, m) {
  n = fs_read(rel, DSL)
  for (i = 1; i <= n; i++) {
    if (index(DSL[i], "extern") && match(DSL[i], /^[ \t]*(pub[ \t]+)?extern[ \t]+fn[ \t]+rt_[A-Za-z0-9_]+/)) {
      m = substr(DSL[i], RSTART, RLENGTH); match(m, /rt_[A-Za-z0-9_]+$/); DECLS[substr(m, RSTART)] = 1
    }
  }
}
# PROV/DEFN keys are "host:sym"; RUSTS and DECLS are plain sets
function hm_scan(    i, rel, hi, h, mode, k, id, b) {
  split("", PROV); split("", DEFN); split("", RUSTS); split("", DECLS)
  split("", FID); split("", VISIT); FIDN = 0; RTN = 0
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (!under(rel, "src/runtime", " test vendor target ")) continue
    if (!(endsw(rel, ".c") || endsw(rel, ".cpp") || endsw(rel, ".m") || endsw(rel, ".mm"))) continue
    if (!owned_rel(rel)) continue
    RTN++; RTID[RTN] = hc_id(rel); RTHOST[RTN] = file_host(rel)
  }
  for (hi = 1; hi <= 5; hi++) {
    h = HL[hi]
    for (mode = 0; mode <= 1; mode++) host_pass(h, mode)
  }
  for (k in DEFN) if (!(k in PROV)) delete DEFN[k]
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (endsw(rel, ".rs") && (under(rel, "src/compiler_rust/runtime/src", " test vendor target ") || \
        under(rel, "src/runtime", " test vendor target "))) scan_rs(rel)
    else if (in_spl_tops(rel, " test vendor target ")) scan_decl_simple(rel)
  }
}
function hm_run(regen,    hosted, nh, hi, h, edges, ne, k, sym, missing, nm, mk, m, anyhost, base, newl, stale, nn, ns, i, n, cnt, hosts_n, line, bl, text, nrs, nnp) {
  hm_scan()
  # edges = (decl & hosted providers) - rust
  split("", EDGES); ne = 0; split("", ANYH)
  for (k in PROV) { sym = substr(k, index(k, ":") + 1); ANYH[sym] = 1 }
  for (sym in DECLS) {
    if (sym in RUSTS) continue
    for (hi = 1; hi <= 4; hi++) if ((HL[hi] ":" sym) in PROV) { EDGES[sym] = 1; ne++; break }
  }
  if (ne == 0) { print "ERROR — nothing was checked (0 extern to C provider edges)"; return 2 }
  split("", MISS); nm = 0
  for (hi = 1; hi <= 4; hi++) for (sym in EDGES) if (!((HL[hi] ":" sym) in PROV)) { MISS[HL[hi] ":" sym] = 1; nm++ }
  if (regen) {
    text = "# Shrink-only. <host>:<extern> with a C provider elsewhere but none on this host.\n"
    n = keys_sorted(MISS, SK)
    for (i = 1; i <= n; i++) text = text SK[i] "\n"
    fs_write(HM_BASELINE, text)
  }
  split("", BASE)
  n = fs_read(HM_BASELINE, BLL)
  for (i = 1; i <= n; i++) { line = trim(BLL[i]); if (line != "" && substr(BLL[i], 1, 1) != "#") BASE[line] = 1 }
  split("", NEWS); split("", STALES)
  for (k in MISS) if (!(k in BASE)) NEWS[k] = 1
  for (k in BASE) if (!(k in MISS)) STALES[k] = 1
  nn = keys_sorted(NEWS, SN); ns = keys_sorted(STALES, SS)
  for (i = 1; i <= nn; i++) print "SRT001 new host gap: " SN[i]
  for (i = 1; i <= ns; i++) print "SRT001 stale baseline row, remove it: " SS[i]
  print "RT_AUDIT host=simpleos map=UNKNOWN compile=UNTESTED link=UNTESTED"
  for (hi = 1; hi <= 4; hi++) {
    h = HL[hi]; cnt = 0
    for (k in MISS) if (substr(k, 1, length(h) + 1) == h ":") cnt++
    printf "RT_AUDIT host=%s map_gaps=%d compile=UNTESTED link=UNTESTED\n", h, cnt
  }
  nrs = 0; nnp = 0
  for (sym in DECLS) { if (sym in RUSTS) nrs++; else if (!(sym in ANYH)) nnp++ }
  printf "coverage edges=%d rust_skipped_UNKNOWN=%d no_provider=%d\n", ne, nrs, nnp
  if (nn + ns > 0) { printf "FAIL — %d finding(s)\n", nn + ns; return 1 }
  printf "PASS — %d edge(s) over %d hosts, 0 new gap(s), simpleos UNKNOWN, mapping evidence only\n", ne, 4
  return 0
}

# ---------------------------------------------------------------- pointer map
function sigdef(line,    w, R, Rt, T, rl) {
  if (line !~ /^[A-Za-z_]/) return ""
  match(line, /^[A-Za-z0-9_]+/); w = substr(line, 1, RLENGTH)
  if (w == "static" || w == "return") return ""
  match(line, /^[A-Za-z0-9_ \t*]*/); rl = RLENGTH
  if (substr(line, rl + 1, 1) != "(") return ""
  Rt = substr(line, 1, rl); sub(/[ \t]+$/, "", Rt)
  if (!match(Rt, /[A-Za-z0-9_]+$/)) return ""
  if (RSTART < 3) return ""
  T = substr(Rt, RSTART)
  if (T !~ /^rt_[A-Za-z0-9_]+$/) return ""
  SCOL = rl + 1
  return T
}
function cdef(line,    w, m, rl) {
  if (line !~ /^[A-Za-z_]/) return ""
  if (!match(line, /^[A-Za-z_][A-Za-z0-9_]*([ \t]+[A-Za-z_][A-Za-z0-9_]*)*[ \t]*\*+[ \t]*rt_[A-Za-z0-9_]+[ \t]*\(/)) return ""
  rl = RLENGTH
  match(line, /^[A-Za-z0-9_]+/); w = substr(line, 1, RLENGTH)
  if (w == "static") return ""
  m = substr(line, 1, rl - 1); sub(/[ \t]+$/, "", m)
  match(m, /[A-Za-z0-9_]+$/)
  SCOL = rl
  return substr(m, RSTART)
}
# closing ')' of the '(' at (li, col); sets CLI, CLC
function close_paren(S, sn, li, col,    depth, i, j, line, len, ch) {
  depth = 0
  for (i = li; i <= sn; i++) {
    line = S[i]; len = length(line)
    for (j = (i == li ? col : 1); j <= len; j++) {
      ch = substr(line, j, 1)
      if (ch == "(") depth++
      else if (ch == ")") { depth--; if (depth == 0) { CLI = i; CLC = j; return 1 } }
    }
  }
  return 0
}
function paren_text(S, li, col, cli, clc,    i, t) {
  if (li == cli) return substr(S[li], col + 1, clc - col - 1)
  t = substr(S[li], col + 1)
  for (i = li + 1; i < cli; i++) t = t "\n" S[i]
  return t "\n" substr(S[cli], 1, clc - 1)
}
# first '{' (BLI, BCOL) or 0 when a ';' at paren depth 0 comes first
function body_find(S, sn, li, col,    paren, i, j, line, len, ch) {
  paren = 0
  for (i = li; i <= sn; i++) {
    line = S[i]; len = length(line)
    for (j = (i == li ? col : 1); j <= len; j++) {
      ch = substr(line, j, 1)
      if (ch == "(") paren++
      else if (ch == ")") paren--
      else if (ch == ";" && paren == 0) return 0
      else if (ch == "{") { BLI = i; BCOL = j; return 1 }
    }
  }
  return 0
}
function grab_body(S, sn, li, col,    depth, i, line, rest, off, ch, cut, body) {
  depth = 0; body = ""
  for (i = li; i <= sn; i++) {
    line = (i == li) ? substr(S[i], col) : S[i]
    rest = line; off = 0
    while (match(rest, /[{}]/)) {
      ch = substr(rest, RSTART, 1)
      depth += (ch == "{") ? 1 : -1
      cut = off + RSTART
      rest = substr(rest, RSTART + 1); off = cut
      if (depth == 0) return body substr(line, 1, cut)
    }
    body = body line "\n"
  }
  return body
}
function classify(body,    t, m, r, nret, allenf) {
  if (match(" " body, RE_NR1) || match(" " body, RE_NR2)) return "nil"
  rest_ = body; nret = 0; allenf = 1
  while (1) {
    t = " " rest_
    if (!match(t, /[^A-Za-z0-9_]return([^A-Za-z0-9_;][^;]*)?;/)) break
    r = substr(t, RSTART + 1, RLENGTH - 1)
    rest_ = substr(t, RSTART + RLENGTH)
    nret++
    if (r !~ RE_ENF) allenf = 0
  }
  if (nret > 0 && allenf) return "enforced"
  return "seen"
}
function len_name(p,    w) {
  if (!match(p, /[A-Za-z0-9_]+$/)) return 0
  w = substr(p, RSTART)
  return (w ~ /(len|length|count|size|cap)$/)
}
function bare_len(p,    w) {
  if (!match(p, /[A-Za-z0-9_]+$/)) return 0
  w = substr(p, RSTART)
  return (w == "n" || w == "kl" || w == "dl")
}
function strip_qual(s,    out, w) {
  out = ""
  while (s != "") {
    if (match(s, /^[A-Za-z0-9_]+/)) {
      w = substr(s, 1, RLENGTH); s = substr(s, RLENGTH + 1)
      out = out ((w ~ /^(const|volatile|restrict|__restrict|struct|enum|union)$/) ? " " : w)
    } else {
      match(s, /^[^A-Za-z0-9_]+/)
      out = out substr(s, 1, RLENGTH); s = substr(s, RLENGTH + 1)
    }
  }
  return out
}
function split_top(text, arr,    n, cur, depth, prev, i, ch, len) {
  n = 0; cur = ""; depth = 0; prev = ""; len = length(text)
  for (i = 1; i <= len; i++) {
    ch = substr(text, i, 1)
    if (ch == "(" || ch == "[" || ch == "{" || ch == "<") depth++
    else if (ch == ")" || ch == "]" || ch == "}" || (ch == ">" && prev != "-")) depth--
    prev = ch
    if (ch == "," && depth == 0) { arr[++n] = cur; cur = "" } else cur = cur ch
  }
  if (trim(cur) != "") arr[++n] = cur
  for (i = 1; i <= n; i++) arr[i] = trim(arr[i])
  return n
}
# C parameter list -> kind string (p ptr, s scalar, u unparsed); fold=1 text ABI fold
function c_params(text, fold,    t, n, parts, i, p, kinds, lastk, lastb, paired, base, k) {
  t = norm_ws(text)
  if (t == "" || t == "void") return ""
  split("", parts); n = split_top(t, parts)
  kinds = ""; lastk = ""; lastb = ""; paired = 0
  for (i = 1; i <= n; i++) {
    p = parts[i]
    if (p == "...") break
    if (fold && kinds != "" && lastk == "p" && (lastb == "uint8_t" || lastb == "char") && !paired && \
        index(p, "*") == 0 && index(p, "(") == 0 && index(p, "[") == 0 && \
        (len_name(p) || (lastb == "uint8_t" && bare_len(p)))) { paired = 1; continue }
    paired = 0
    if (index(p, "(") || index(p, "[")) { kinds = kinds "u"; lastk = "u"; lastb = p }
    else if (index(p, "*")) {
      k = 0
      for (i2 = length(p); i2 >= 1; i2--) if (substr(p, i2, 1) == "*") { k = i2; break }
      base = norm_ws(strip_qual(substr(p, 1, k - 1)))
      kinds = kinds "p"; lastk = "p"; lastb = base
    } else { kinds = kinds "s"; lastk = "s"; lastb = p }
  }
  return kinds
}
function spl_type(typ,    p, s) {
  p = index(typ, "="); if (p) typ = substr(typ, 1, p - 1)
  typ = trim(typ)
  if (typ ~ /^Option<.+>$/) { ST_K = "opt"; ST_B = trim(substr(typ, 8, length(typ) - 8)); return }
  if (substr(typ, 1, 1) == "&") {
    s = substr(typ, 2); sub(/^[[:space:]]+/, "", s)
    if (substr(s, 1, 3) == "mut" && substr(s, 4, 1) !~ /[A-Za-z0-9_]/) { ST_K = "refmut"; ST_B = trim(substr(s, 4)); return }
    ST_K = "ref"; ST_B = trim(s); return
  }
  if (substr(typ, length(typ), 1) == "?") { ST_K = "opt"; ST_B = trim(substr(typ, 1, length(typ) - 1)); return }
  ST_K = "bare"; ST_B = typ
}
function spl_params(text,    t, n, parts, i, p, typ) {
  t = norm_ws(text); split("", parts); n = split_top(t, parts)
  for (i = 1; i <= n; i++) {
    p = parts[i]
    if (!index(p, ":")) { SPK[i] = ""; SPB[i] = ""; SPT[i] = "" }
    else { typ = trim(substr(p, index(p, ":") + 1)); spl_type(typ); SPK[i] = ST_K; SPB[i] = ST_B; SPT[i] = typ }
  }
  return n
}
function addunp(rel, sym, i,    k) { k = rel SUBSEP sym SUBSEP i; if (!(k in PUNP)) { PUNP[k] = 1 } }
function addptr(rel, sym, i,    k) { k = rel SUBSEP sym SUBSEP i; if (!(k in PPTR)) { PPTR[k] = 1 } }
function join_params(sym, params, rel,    spn, k, e, parts, fk, rk, sig, i, ck, key, sb) {
  spn = spl_params(params)
  for (k = 1; k <= SIGN[sym]; k++) {
    e = SIGENT[sym, k]
    if (e == "\001") { addunp(rel, sym, -1); continue }
    split(e, parts, ":"); fk = parts[1]; rk = parts[2]
    sig = (length(rk) == spn) ? rk : fk
    if (length(sig) != spn) { SRT003[rel ":" sym " C=" length(rk) " spl=" spn] = 1; continue }
    for (i = 1; i <= spn; i++) {
      ck = substr(sig, i, 1)
      if (ck == "u" || SPK[i] == "") { addunp(rel, sym, i - 1); continue }
      if (ck != "p") continue
      addptr(rel, sym, i - 1)
      key = rel ":" sym ":" (i - 1) ":" SPT[i]
      sb = SPB[i]; sub(/\?+$/, "", sb)
      if (sb in NAR) PNARROW[key] = 1
      else if (SPK[i] == "opt") SNULL[key] = "SNULL002"
      else if (SPK[i] == "ref" || SPK[i] == "refmut") SNULL[key] = "SNULL003"
    }
  }
}
# C pointer-return states (shared by ptr and index modes); sigs only when want_sigs
function c_scan(want_sigs,    i, rel, n, txt, S, sn, li, nm, ok, par, state, body, kind) {
  split("", CSTATE); split("", SIGN); split("", SIGENT)
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (!(endsw(rel, ".c") || endsw(rel, ".h")) || !under(rel, "src/runtime", " test ")) continue
    n = fs_read(rel, CRL)
    txt = strip_c(CRL, n, 0, 1, 0)
    txt = strip_attr(txt, "", 1)
    sn = split(txt, S, "\n"); if (sn > 0 && S[sn] == "") sn--
    for (li = 1; li <= sn; li++) {
      if (want_sigs) {
        nm = sigdef(S[li])
        if (nm != "") {
          SIGN[nm]++
          ok = close_paren(S, sn, li, SCOL)
          if (ok) { par = paren_text(S, li, SCOL, CLI, CLC); SIGENT[nm, SIGN[nm]] = c_params(par, 1) ":" c_params(par, 0) }
          else SIGENT[nm, SIGN[nm]] = "\001"
        }
      }
      nm = cdef(S[li])
      if (nm == "") continue
      state = (nm in CSTATE) ? CSTATE[nm] : "unknown"
      if (body_find(S, sn, li, SCOL)) {
        body = grab_body(S, sn, BLI, BCOL)
        kind = classify(body)
        if (RANK[kind] > RANK[state]) state = kind
      }
      CSTATE[nm] = state
    }
  }
}
# one `extern fn rt_*` record found in a .spl file
function ext_record(rel, sym, params, hasret, ret,    ty, key, base) {
  if (EXTMODE == "index") {
    XN++; XSYM[XN] = sym; XPAR[XN] = params; XRET[XN] = hasret ? ret : "void"; XPATH[XN] = rel
    return
  }
  if (sym in SIGN) { P_PEDGES++; join_params(sym, params, rel) }
  if (!(sym in CSTATE)) return
  P_EDGES++
  ty = hasret ? ret : "void"
  key = rel ":" sym ":" ty
  base = ty; sub(/\?+$/, "", base)
  if (base in NAR) PNARROWR[key] = 1
  else if (base == "i64" || base == "u64" || base == "usize" || base == "isize" || base == "void") P_RAW++
  else if (substr(ty, length(ty), 1) == "?") return
  else if (CSTATE[sym] == "nil") NILS[key] = 1
  else if (CSTATE[sym] == "enforced") P_ENF++
  else P_UNK++
}
# PM.EXT finditer over one file's lines
function ext_scan_file(rel, L, n,    i, line, pre, nm, col, j, k, ch, depth, params, endl, endc, ok, rest, ret, hasret, t, p, gen) {
  i = 1
  while (i <= n) {
    line = L[i]
    if (!index(line, "extern") || !match(line, /^[ \t]*(pub[ \t]+)?extern[ \t]+fn[ \t]+rt_[A-Za-z0-9_]+/)) { i++; continue }
    pre = RLENGTH
    match(substr(line, 1, pre), /rt_[A-Za-z0-9_]+$/); nm = substr(line, RSTART, RLENGTH)
    col = pre + 1
    if (substr(line, col, 1) == "<") {
      p = index(substr(line, col), ">")
      if (!p) { i++; continue }
      col += p
    }
    match(substr(line, col), /^[ \t]*/); col += RLENGTH
    if (substr(line, col, 1) != "(") { i++; continue }
    # params: (non-paren | '(' nonparen* ')')* up to the closing ')'
    j = i; k = col + 1; depth = 0; params = ""; ok = 0
    while (j <= n) {
      line = L[j]
      while (k <= length(line)) {
        ch = substr(line, k, 1)
        if (ch == "(") { if (depth == 1) { j = n + 1; break } depth = 1; params = params ch }
        else if (ch == ")") {
          if (depth == 1) { depth = 0; params = params ch }
          else { ok = 1; endl = j; endc = k; break }
        } else params = params ch
        k++
      }
      if (ok || j > n) break
      params = params "\n"; j++; k = 1
    }
    if (!ok) { i++; continue }
    rest = substr(L[endl], endc + 1); sub(/^[ \t]+/, "", rest)
    hasret = 0; ret = ""
    if (rest == "" || substr(rest, 1, 1) == "#") { }
    else if (substr(rest, 1, 2) == "->") {
      t = substr(rest, 3); p = index(t, "#"); if (p) t = substr(t, 1, p - 1)
      if (t == "") { i++; continue }
      hasret = 1; ret = trim(t)
    } else { i++; continue }
    ext_record(rel, nm, params, hasret, ret)
    i = endl + 1
  }
}
function ptr_scan(    i, rel, n, L) {
  split("", NILS); split("", PNARROWR); split("", PUNP); split("", PPTR); split("", SRT003); split("", PNARROW); split("", SNULL)
  P_EDGES = 0; P_UNK = 0; P_RAW = 0; P_ENF = 0; P_PEDGES = 0
  EXTMODE = "ptr"
  c_scan(1)
  P_SYMS = set_count(CSTATE)
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (!in_spl_tops(rel, " test ")) continue
    n = fs_read(rel, SPL)
    ext_scan_file(rel, SPL, n)
  }
}
function ptr_run(regen, regen_param,    syms, edges, n, i, k, bl, text, new_n, stale_n, nl, nb, base, new_, stale_, pbase, pnew, pstale, cbase, cnew, cstale, nmp, srt, ns, c2, c3, bad, baselined, pbl, snull2, sn2, nn) {
  ptr_scan()
  syms = P_SYMS; edges = P_EDGES
  if (syms == 0 || edges == 0) { print "ERROR — nothing was checked (0 C pointer symbols or 0 extern edges)"; return 2 }
  if (regen) {
    text = "# Shrink-only. <file>:<extern>:<type> where C can return NULL and .spl is non-optional.\n"
    n = keys_sorted(NILS, SK); for (i = 1; i <= n; i++) text = text SK[i] "\n"
    fs_write(PM_BASELINE, text)
  }
  split("", BASE); bl_load(PM_BASELINE, BASE)
  split("", NEW1); split("", STALE1)
  for (k in NILS) if (!(k in BASE)) NEW1[k] = 1
  for (k in BASE) if (!(k in NILS)) STALE1[k] = 1
  new_n = keys_sorted(NEW1, SN); stale_n = keys_sorted(STALE1, SS)
  nl = keys_sorted(PNARROWR, SK)
  for (i = 1; i <= nl; i++) print "SRT004 narrow pointer return: " SK[i]
  for (i = 1; i <= new_n; i++) print "SRT004 new nil mismatch: " SN[i]
  for (i = 1; i <= stale_n; i++) print "SRT004 stale baseline row, remove it: " SS[i]
  baselined = 0; for (k in NILS) if (k in BASE) baselined++
  printf "coverage symbols=%d edges=%d enforced=%d baselined=%d raw=%d UNKNOWN=%d compile=UNTESTED link=UNTESTED\n", syms, edges, P_ENF, baselined, P_RAW, P_UNK
  if (regen_param) {
    text = "# Shrink-only. <file>:<extern>:<param_index>:<type> where a .spl T? (SNULL002) or &T/&mut T (SNULL003) crosses a bare C T* parameter.\n"
    n = keys_sorted(SNULL, SK); for (i = 1; i <= n; i++) text = text SK[i] "\n"
    fs_write(PP_BASELINE, text)
  }
  split("", PB); bl_load(PP_BASELINE, PB)
  split("", PNEW1); split("", PSTALE1)
  for (k in SNULL) if (!(k in PB)) PNEW1[k] = 1
  for (k in PB) if (!(k in SNULL)) PSTALE1[k] = 1
  pnew = keys_sorted(PNEW1, PNS); pstale = keys_sorted(PSTALE1, PSS)
  srt = keys_sorted(SRT003, SR3)
  if (regen_param) {
    text = "# Shrink-only. SRT003: <file>:<extern> C=<n> spl=<n>; these params are not joined.\n"
    for (i = 1; i <= srt; i++) text = text SR3[i] "\n"
    fs_write(PC_BASELINE, text)
  }
  split("", CB); bl_load(PC_BASELINE, CB)
  split("", CNEW1); split("", CSTALE1)
  for (k in SRT003) if (!(k in CB)) CNEW1[k] = 1
  for (k in CB) if (!(k in SRT003)) CSTALE1[k] = 1
  cnew = keys_sorted(CNEW1, CNS); cstale = keys_sorted(CSTALE1, CSS)
  for (i = 1; i <= cnew; i++) print "SRT003 new param count mismatch: " CNS[i]
  for (i = 1; i <= cstale; i++) print "SRT003 stale baseline row, remove it: " CSS[i]
  nmp = keys_sorted(PNARROW, PNR)
  for (i = 1; i <= nmp; i++) print "SRT004 narrow pointer param: " PNR[i]
  for (i = 1; i <= pnew; i++) print SNULL[PNS[i]] " new param mismatch: " PNS[i]
  for (i = 1; i <= pstale; i++) print "SNULL stale param baseline row, remove it: " PSS[i]
  c2 = 0; c3 = 0; baselined = 0
  for (k in SNULL) { if (SNULL[k] == "SNULL002") c2++; else if (SNULL[k] == "SNULL003") c3++; if (k in PB) baselined++ }
  printf "param coverage: edges=%d ptr_params=%d unparsed=%d SRT003=%d narrow=%d SNULL002=%d SNULL003=%d baselined=%d\n", P_PEDGES, set_count(PPTR), set_count(PUNP), srt, nmp, c2, c3, baselined
  bad = nl + new_n + stale_n + nmp + pnew + pstale + cnew + cstale
  if (bad) { printf "FAIL — %d edge(s) checked, %d finding(s)\n", edges, bad; return 1 }
  printf "PASS — %d edge(s) checked, 0 new finding(s), mapping evidence only\n", edges
  return 0
}
function bl_load(rel, S,    n, i, t) {
  n = fs_read(rel, BLL)
  for (i = 1; i <= n; i++) { t = trim(BLL[i]); if (t != "" && substr(BLL[i], 1, 1) != "#") S[t] = 1 }
}

# ---------------------------------------------------------------- sha256 (first 16 hex)
function hex2n(h,    i, v) { v = 0; for (i = 1; i <= length(h); i++) v = v * 16 + index("0123456789abcdef", substr(h, i, 1)) - 1; return v }
function sha_init(    a, b, i, ks, n, hs) {
  A8[0] = 0
  for (a = 0; a < 256; a++) for (b = 0; b < 256; b++) {
    if (a == 0 || b == 0) A8[a * 256 + b] = 0
    else A8[a * 256 + b] = (a % 2) * (b % 2) + 2 * A8[int(a / 2) * 256 + int(b / 2)]
  }
  ks = "428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5 d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174 e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da 983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967 27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85 a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070 19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3 748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2"
  n = split(ks, hs, " ")
  for (i = 1; i <= n; i++) K256[i - 1] = hex2n(hs[i])
  for (i = 0; i < 256; i++) ORD[sprintf("%c", i)] = i
  P2[0] = 1; for (i = 1; i <= 32; i++) P2[i] = P2[i - 1] * 2
  SHA_OK = 1
}
function and32(a, b) {
  return A8[(a % 256) * 256 + (b % 256)] + \
    256 * A8[(int(a / 256) % 256) * 256 + (int(b / 256) % 256)] + \
    65536 * A8[(int(a / 65536) % 256) * 256 + (int(b / 65536) % 256)] + \
    16777216 * A8[int(a / 16777216) * 256 + int(b / 16777216)]
}
function xor32(a, b) { return a + b - 2 * and32(a, b) }
function rotr(x, n) { return int(x / P2[n]) + (x % P2[n]) * P2[32 - n] }
function shr(x, n) { return int(x / P2[n]) }
function hex8(x,    s, i) { s = ""; for (i = 0; i < 8; i++) { s = substr("0123456789abcdef", x % 16 + 1, 1) s; x = int(x / 16) } return s }
function sha256_16(msg,    len, bytes, i, nb, blk, w, t, a, b, c, d, e, f, g, h, h0, h1, h2, h3, h4, h5, h6, h7, s0, s1, ch, maj, t1, t2, M, nblk, off) {
  if (!SHA_OK) sha_init()
  len = length(msg); nb = 0
  for (i = 1; i <= len; i++) M[nb++] = ORD[substr(msg, i, 1)]
  M[nb++] = 128
  while (nb % 64 != 56) M[nb++] = 0
  t = len * 8
  for (i = 7; i >= 0; i--) { M[nb + i] = t % 256; t = int(t / 256) }
  nb += 8
  h0 = hex2n("6a09e667"); h1 = hex2n("bb67ae85"); h2 = hex2n("3c6ef372"); h3 = hex2n("a54ff53a")
  h4 = hex2n("510e527f"); h5 = hex2n("9b05688c"); h6 = hex2n("1f83d9ab"); h7 = hex2n("5be0cd19")
  for (off = 0; off < nb; off += 64) {
    for (i = 0; i < 16; i++) w[i] = ((M[off + 4 * i] * 256 + M[off + 4 * i + 1]) * 256 + M[off + 4 * i + 2]) * 256 + M[off + 4 * i + 3]
    for (i = 16; i < 64; i++) {
      s0 = xor32(xor32(rotr(w[i - 15], 7), rotr(w[i - 15], 18)), shr(w[i - 15], 3))
      s1 = xor32(xor32(rotr(w[i - 2], 17), rotr(w[i - 2], 19)), shr(w[i - 2], 10))
      w[i] = (w[i - 16] + s0 + w[i - 7] + s1) % 4294967296
    }
    a = h0; b = h1; c = h2; d = h3; e = h4; f = h5; g = h6; h = h7
    for (i = 0; i < 64; i++) {
      s1 = xor32(xor32(rotr(e, 6), rotr(e, 11)), rotr(e, 25))
      ch = xor32(g, and32(e, xor32(f, g)))
      t1 = (h + s1 + ch + K256[i] + w[i]) % 4294967296
      s0 = xor32(xor32(rotr(a, 2), rotr(a, 13)), rotr(a, 22))
      maj = xor32(and32(a, b), and32(c, xor32(a, b)))
      t2 = (s0 + maj) % 4294967296
      h = g; g = f; f = e; e = (d + t1) % 4294967296; d = c; c = b; b = a; a = (t1 + t2) % 4294967296
    }
    h0 = (h0 + a) % 4294967296; h1 = (h1 + b) % 4294967296; h2 = (h2 + c) % 4294967296; h3 = (h3 + d) % 4294967296
    h4 = (h4 + e) % 4294967296; h5 = (h5 + f) % 4294967296; h6 = (h6 + g) % 4294967296; h7 = (h7 + h) % 4294967296
  }
  return hex8(h0) hex8(h1)
}

# ---------------------------------------------------------------- binding index
function canonical_signature(params, ret,    parts, n, i, p, out, r) {
  split("", parts); n = split_top(norm_ws(params), parts)
  out = ""
  for (i = 1; i <= n; i++) {
    p = parts[i]
    if (index(p, ":")) p = trim(substr(p, index(p, ":") + 1))
    out = out (i > 1 ? ", " : "") norm_ws(p)
  }
  r = norm_ws(ret); if (r == "") r = "void"
  return "(" out ") -> " r
}
function provider_state(h, sym) {
  if (!(h in ISHOSTED)) return "unknown"
  if ((h ":" sym) in DEFN) return "mapped"
  if ((h ":" sym) in PROV) return "conditional"
  return "unknown"
}
function map_verdict(sym, st,    hi, got) {
  if (sym in RUSTS) { MV = "UNKNOWN"; MR = "rust-export, cfg not evaluated"; return }
  for (hi = 1; hi <= 4; hi++) if (st[hi] == "conditional") { MV = "UNKNOWN"; MR = "conditional-provider-on-hosted-profile"; return }
  got = 0
  for (hi = 1; hi <= 4; hi++) if (st[hi] == "mapped") got++
  if (got == 0) { MV = "UNKNOWN"; MR = "no-c-provider-in-scan"; return }
  if (got == 4) { MV = "PASS"; MR = "mapped-on-all-hosted-profiles"; return }
  MV = "FAIL"; MR = "host-gap-on-" (4 - got) "-hosted-profile(s)"
}
function pointer_verdict(sym, ty,    base) {
  if (!(sym in CSTATE)) { PV = "UNKNOWN"; PVR = "no-c-pointer-definition"; return }
  base = ty; sub(/\?+$/, "", base)
  if (base in NAR) { PV = "FAIL"; PVR = "narrow-pointer"; return }
  if (base == "i64" || base == "u64" || base == "usize" || base == "isize" || base == "void") { PV = "UNKNOWN"; PVR = "raw-handle"; return }
  if (substr(ty, length(ty), 1) == "?") {
    if (CSTATE[sym] == "nil") { PV = "PASS"; PVR = "nullable-declared"; return }
    PV = "UNKNOWN"; PVR = "nullable-declared-c-unproven"; return
  }
  if (CSTATE[sym] == "nil") { PV = "FAIL"; PVR = "nil-mismatch"; return }
  if (CSTATE[sym] == "enforced") { PV = "PASS"; PVR = "enforced"; return }
  PV = "UNKNOWN"; PVR = "c-return-unproven"
}
# scan all spl files once: extern records (tops) and, for contract mode, type names (all of src/)
function spl_pass(want_types,    i, rel, n, L, intop, insrc, j, line, m, nm, tg) {
  XN = 0; EXTMODE = "index"
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (!endsw(rel, ".spl")) continue
    intop = in_spl_tops(rel, " test vendor target ")
    insrc = want_types && startsw(rel, "src/")
    if (!intop && !insrc) continue
    n = fs_read(rel, SPL)
    if (intop) ext_scan_file(rel, SPL, n)
    if (insrc) {
      for (j = 1; j <= n; j++) {
        line = SPL[j]
        if (line !~ /^[ \t]*(pub[ \t]+)?(class|struct|enum|type)[ \t]/) continue
        if (match(line, /^[ \t]*(pub[ \t]+)?(class|struct|enum)[ \t]+[A-Za-z_][A-Za-z0-9_]*/)) {
          m = substr(line, RSTART, RLENGTH); match(m, /[A-Za-z0-9_]+$/); NOM[substr(m, RSTART)] = 1
        }
        if (match(line, /^[ \t]*(pub[ \t]+)?type[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*=[ \t]*[A-Za-z_][A-Za-z0-9_]*[ \t]*$/)) {
          m = substr(line, RSTART, RLENGTH)
          sub(/^[ \t]*(pub[ \t]+)?type[ \t]+/, "", m)
          match(m, /^[A-Za-z0-9_]+/); nm = substr(m, 1, RLENGTH)
          m = substr(m, RLENGTH + 1); sub(/^[ \t]*=[ \t]*/, "", m); sub(/[ \t]+$/, "", m)
          tg = m
          if (tg in SCALAR) ALIAS[nm] = tg
        }
      }
    }
  }
}
function index_build(want_types,    i, k, n, sym, sig, states, hi, h, rec, tally, keys, nrec, ord, t) {
  split("", NOM); split("", ALIAS); split("", RECS)
  hm_scan()
  c_scan(0)
  spl_pass(want_types)
  if (want_types) {
    for (k in ALIAS) if (k in NOM) { delete ALIAS[k]; delete NOM[k] }
  }
  nrec = XN
  for (i = 1; i <= XN; i++) {
    sym = XSYM[i]
    sig = canonical_signature(XPAR[i], XRET[i])
    XSIG[i] = sig
    for (hi = 1; hi <= 5; hi++) { h = HL[hi]; ST5[hi] = provider_state(h, sym) }
    map_verdict(sym, ST5); XMV[i] = MV; XMR[i] = MR
    pointer_verdict(sym, XRET[i]); XPV[i] = PV; XPR[i] = PVR
    for (hi = 1; hi <= 5; hi++) XST[i, hi] = ST5[hi]
    KEYS[i] = XPATH[i] "\001" sym "\001" sig "\001" i
  }
  msort(KEYS, XN)
  for (i = 1; i <= XN; i++) { t = KEYS[i]; sub(/^.*\001/, "", t); ORD2[i] = t + 0 }
}
function jstr(s,    out, i, c, n) {
  if (s ~ /[^ -~]/) { NONASCII = 1 }
  gsub(/\\/, "\\\\", s); gsub(/"/, "\\\"", s)
  return "\"" s "\""
}
function jl(s) { JD[++JDN] = s }
function index_render(    i, r, hi, t, mp, mf, mu, pp, pf, pu, v) {
  JDN = 0; split("", JD); NONASCII = 0
  mp = 0; mf = 0; mu = 0; pp = 0; pf = 0; pu = 0
  for (i = 1; i <= XN; i++) {
    v = XMV[i]; if (v == "PASS") mp++; else if (v == "FAIL") mf++; else mu++
    v = XPV[i]; if (v == "PASS") pp++; else if (v == "FAIL") pf++; else pu++
  }
  jl("{")
  jl("  \"host_notes\": {")
  jl("    \"simpleos\": \"no C macro selects SimpleOS; always unknown, never mapped\"")
  jl("  },")
  jl("  \"map_scope\": [")
  jl("    \"linux\",")
  jl("    \"macos\",")
  jl("    \"windows\",")
  jl("    \"freebsd\"")
  jl("  ],")
  if (XN == 0) jl("  \"records\": [],")
  else {
    jl("  \"records\": [")
    for (i = 1; i <= XN; i++) {
      r = ORD2[i]
      jl("    {")
      jl("      \"id\": " jstr(sha256_16(XSYM[r] "\n" XSIG[r])) ",")
      jl("      \"path\": " jstr(XPATH[r]) ",")
      jl("      \"providers\": [")
      for (hi = 1; hi <= 5; hi++) {
        jl("        {")
        jl("          \"host\": " jstr(HL[hi]) ",")
        jl("          \"state\": " jstr(XST[r, hi]))
        jl("        }" (hi < 5 ? "," : ""))
      }
      jl("      ],")
      jl("      \"signature\": " jstr(XSIG[r]) ",")
      jl("      \"symbol\": " jstr(XSYM[r]) ",")
      jl("      \"verdict\": {")
      jl("        \"compile\": \"UNTESTED\",")
      jl("        \"link\": \"UNTESTED\",")
      jl("        \"map\": " jstr(XMV[r]) ",")
      jl("        \"map_reason\": " jstr(XMR[r]) ",")
      jl("        \"pointer\": " jstr(XPV[r]) ",")
      jl("        \"pointer_reason\": " jstr(XPR[r]))
      jl("      }")
      jl("    }" (i < XN ? "," : ""))
    }
    jl("  ],")
  }
  jl("  \"schema\": \"rt-binding-index\",")
  jl("  \"summary\": {")
  jl("    \"compile\": \"UNTESTED\",")
  jl("    \"link\": \"UNTESTED\",")
  jl("    \"records\": " XN ",")
  jl("    \"tally\": {")
  jl("      \"map\": {")
  jl("        \"FAIL\": " mf ",")
  jl("        \"PASS\": " mp ",")
  jl("        \"UNKNOWN\": " mu)
  jl("      },")
  jl("      \"pointer\": {")
  jl("        \"FAIL\": " pf ",")
  jl("        \"PASS\": " pp ",")
  jl("        \"UNKNOWN\": " pu)
  jl("      }")
  jl("    }")
  jl("  },")
  jl("  \"version\": 1")
  jl("}")
  T_MP = mp; T_MF = mf; T_MU = mu; T_PP = pp; T_PF = pf; T_PU = pu
}
function jd_text(    i, s) { s = ""; for (i = 1; i <= JDN; i++) s = s JD[i] "\n"; return s }
function index_main(    i, dest) {
  index_build(0)
  if (XN == 0) { print "ERROR — nothing was checked (0 extern records)"; return 2 }
  index_render()
  if (NONASCII) { print "ERROR — non-ASCII byte in an index string value (not escaped by this port)"; return 2 }
  if (OUTP_ != "") { for (i = 1; i <= JDN; i++) print JD[i] > OUTP_; close(OUTP_); dest = OUTP_ }
  else { for (i = 1; i <= JDN; i++) print JD[i]; dest = "stdout" }
  printf "RT_BINDING_INDEX version=1 records=%d map=PASS:%d/FAIL:%d/UNKNOWN:%d pointer=PASS:%d/FAIL:%d/UNKNOWN:%d compile=UNTESTED link=UNTESTED out=%s\n", XN, T_MP, T_MF, T_MU, T_PP, T_PF, T_PU, dest > "/dev/stderr"
  return 0
}

# ---------------------------------------------------------------- C contract compile
function c_type(t,    base) {
  if (t in SCALAR) return SCALAR[t]
  if (t in ALIAS) return SCALAR[ALIAS[t]]
  if (t == "text" || is_handle(t)) return "int64_t"
  if (substr(t, length(t), 1) == "?" && c_type(substr(t, 1, length(t) - 1)) != "") return "int64_t"
  return ""
}
function is_handle(t) {
  if (substr(t, 1, 1) == "[" && substr(t, length(t), 1) == "]" && length(t) > 2) return 1
  if (t ~ /^Vec[0-9]+[fdiu][0-9]*$/) return 1
  return (t in NOM)
}
function first_error_arr(T, n,    i, l) {
  for (i = 1; i <= n; i++) if (index(T[i], "error")) return substr(trim(T[i]), 1, 240)
  for (i = 1; i <= n; i++) if (trim(T[i]) != "") return substr(trim(T[i]), 1, 240)
  return "<no output>"
}
function names_symbol(T, n, sym,    i) {
  for (i = 1; i <= n; i++) if (index(T[i], "error") && index(T[i], "'" sym "'")) return 1
  return 0
}
# run a shell command line, capture stdout+stderr lines in RC_T[1..RC_N]; returns exit status
function run_cc(cmd,    f1, f2, rc, line, k) {
  RC_SEQ++
  f1 = TMPD "/rc_" RC_SEQ ".out"; f2 = TMPD "/rc_" RC_SEQ ".err"
  rc = system(CCTO cmd " > " q(f1) " 2> " q(f2))
  RC_N = 0; split("", RC_T)
  while ((getline line < f1) > 0) { sub(/\r$/, "", line); RC_T[++RC_N] = line }
  close(f1)
  while ((getline line < f2) > 0) { sub(/\r$/, "", line); RC_T[++RC_N] = line }
  close(f2)
  return rc
}
function cc_argv(    ) { return CC " -std=gnu11 -I " q(ROOT "/src/runtime") }
function defined_symbols_text(txt, set,    S, sn, i, nm) {
  txt = strip_attr(txt, "", 1)
  sn = split(txt, S, "\n"); if (sn > 0 && S[sn] == "") sn--
  provider_defs(S, sn, set, "")
}
function raw_defs(tu_abs, set,    n, txt, L) {
  split("", set)
  n = fs_read(tu_abs, RDL)
  if (n < 0) return
  txt = strip_c(RDL, n, 0, 1, 0)
  defined_symbols_text(txt, set)
}
function parse_sig(sig,    p, last, k, rest, m1) {
  # ^\((.*)\) -> (.+)$ : greedy, last ") -> " with something after it
  if (substr(sig, 1, 1) != "(") return 0
  last = 0; k = 0
  rest = sig
  while ((p = index(rest, ") -> ")) > 0) { k += p; if (length(sig) > k + 4) last = k; rest = substr(rest, p + 1) }
  if (!last) return 0
  m1 = substr(sig, 2, last - 2)
  PS_RET = trim(substr(sig, last + 5))
  split("", PS_P); PS_N = 0
  if (trim(m1) != "") { PS_N = split(m1, PS_P, ","); for (p = 1; p <= PS_N; p++) PS_P[p] = trim(PS_P[p]) }
  return 1
}
function unmapped(    i) {
  for (i = 1; i <= PS_N; i++) if (c_type(PS_P[i]) == "") return PS_P[i]
  if (PS_RET != "void" && c_type(PS_RET) == "") return PS_RET
  return ""
}
function prototype(sym,    ret_c, ps, i, p, s) {
  ret_c = (PS_RET == "void") ? "void" : c_type(PS_RET)
  ps = ""; s = ""
  for (i = 1; i <= PS_N; i++) {
    p = PS_P[i]
    if (p == "text" && (sym SUBSEP (i - 1)) in SPLIT) { s = "const uint8_t*, uint64_t" }
    else s = c_type(p)
    ps = ps (i > 1 ? ", " : "") s
  }
  return ret_c " " sym "(" (ps == "" ? "void" : ps) ");"
}
function row(sym, sig, spl, tu, cv, reason, diag) {
  RW++; RWK[RW] = tu "\001" sym "\001" sig "\001" RW
  RWsym[RW] = sym; RWsig[RW] = sig; RWspl[RW] = spl; RWtu[RW] = tu; RWc[RW] = cv; RWr[RW] = reason; RWd[RW] = diag
}
function compile_with(tu_abs, protos, np, psyms,    hdr, i) {
  HDRN++
  hdr = TMPD "/rt_c_contract_" HDRN ".h"
  printf "/* generated by check-rt-c-contract-compile.shs from .spl extern signatures */\n" > hdr
  printf "#include <stdint.h>\n#include <stddef.h>\n#include <stdbool.h>\n" > hdr
  for (i = 1; i <= np; i++) print protos[psyms[i]] > hdr
  close(hdr)
  return run_cc(cc_argv() " -fsyntax-only -include " q(hdr) " " q(tu_abs))
}
# judge_protos: PR[sym] = PASS|FAIL|UNTESTED, PRD[sym] = diag. protos[sym] -> text; syms list ss[1..ns]
function judge_protos(tu_abs, protos, ss, ns,    rem, nr, i, rc, named, nn, s, k, rem2, n2, err_first, e2) {
  split("", PR); split("", PRD)
  nr = 0; for (i = 1; i <= ns; i++) REM[++nr] = ss[i]
  while (nr > 0) {
    rc = compile_with(tu_abs, protos, nr, REM)
    if (rc == 0) { for (i = 1; i <= nr; i++) { PR[REM[i]] = "PASS"; PRD[REM[i]] = "" } break }
    err_first = first_error_arr(RC_T, RC_N)
    # copy error text for repeated name checks
    split("", ERRT); for (i = 1; i <= RC_N; i++) ERRT[i] = RC_T[i]; ERRN = RC_N
    nn = 0; split("", NAMED)
    for (i = 1; i <= nr; i++) if (names_symbol(ERRT, ERRN, REM[i])) NAMED[++nn] = REM[i]
    if (nn == 0) { for (i = 1; i <= nr; i++) { PR[REM[i]] = "UNTESTED"; PRD[REM[i]] = "unattributed-error: " err_first } break }
    split("", ONE); split("", ONEL)
    for (i = 1; i <= nn; i++) {
      s = NAMED[i]; ONEL[1] = s
      rc = compile_with(tu_abs, protos, 1, ONEL)
      if (rc != 0 && names_symbol(RC_T, RC_N, s)) { PR[s] = "FAIL"; PRD[s] = first_error_arr(RC_T, RC_N) }
      else { PR[s] = "UNTESTED"; PRD[s] = "unconfirmed-batch-error: " err_first }
    }
    split("", NAMEDSET); for (i = 1; i <= nn; i++) NAMEDSET[NAMED[i]] = 1
    n2 = 0; split("", REM2)
    for (i = 1; i <= nr; i++) if (!(REM[i] in NAMEDSET)) REM2[++n2] = REM[i]
    split("", REM); nr = n2; for (i = 1; i <= nr; i++) REM[i] = REM2[i]
  }
}
function judge_tu(tu_rel, symlist, nsym,    tu_abs, nc, i, s, j, base_fail, rc, pp, ppn, active, k, np, cands, sg, spl, bad, key, nt, pkeys, rank, maxrank, kk, ss, ns, protos, keysr, e, parts, sigs, nsig, verdict) {
  tu_abs = isabs(tu_rel) ? tu_rel : ROOT "/" tu_rel
  split("", DEFSET); raw_defs(tu_abs, DEFSET)
  nc = 0; split("", cands)
  for (i = 1; i <= nsym; i++) if (symlist[i] in DEFSET) cands[++nc] = symlist[i]
  base_fail = ""
  if (fs_read(tu_abs, TMPL) < 0) base_fail = "tu-missing"
  else {
    rc = run_cc(cc_argv() " -E " q(tu_abs))
    split("", PPL); ppn = RC_N; for (i = 1; i <= RC_N; i++) PPL[i] = RC_T[i]
    if (rc != 0) base_fail = "tu-baseline-failed: " first_error_arr(RC_T, RC_N)
    else {
      rc = run_cc(cc_argv() " -fsyntax-only " q(tu_abs))
      if (rc != 0) base_fail = "tu-baseline-failed: " first_error_arr(RC_T, RC_N)
    }
  }
  if (base_fail != "") {
    for (i = 1; i <= nc; i++) {
      s = cands[i]
      nsig = by_sorted(s, sigs)
      for (j = 1; j <= nsig; j++) { split(sigs[j], parts, "\001"); row(s, parts[1], parts[2], tu_rel, "UNTESTED", base_fail, "") }
    }
    return
  }
  split("", ACTIVE)
  txt_ = ""; for (i = 1; i <= ppn; i++) txt_ = txt_ PPL[i] "\n"
  defined_symbols_text(txt_, ACTIVE)
  split("", TESTP); split("", TESTSPL); split("", TESTN); nt = 0; split("", TKEYS)
  for (i = 1; i <= nc; i++) {
    s = cands[i]
    nsig = by_sorted(s, sigs)
    for (j = 1; j <= nsig; j++) {
      split(sigs[j], parts, "\001"); sg = parts[1]; spl = parts[2]
      parse_sig(sg)
      bad = unmapped()
      if (bad != "") row(s, sg, spl, tu_rel, "UNTESTED", "unmapped-spl-type:" bad, "")
      else if (!(s in ACTIVE)) row(s, sg, spl, tu_rel, "UNTESTED", "not-defined-on-host", "")
      else {
        key = s "\001" sg
        if (!(key in TESTP)) { TESTP[key] = prototype(s); TESTN[key] = 0; TKEYS[++nt] = key }
        TESTN[key]++; TESTSPL[key, TESTN[key]] = spl
      }
    }
  }
  # rank: k-th distinct testable signature of a symbol goes in pass k
  split("", RANKV); maxrank = -1
  msort(TKEYS, nt)
  for (i = 1; i <= nt; i++) {
    split(TKEYS[i], parts, "\001"); s = parts[1]
    if ((s in SYMRANK) && SYMRANKTU[s] == tu_rel) RANKV[TKEYS[i]] = ++SYMRANK[s]
    else { SYMRANK[s] = 0; SYMRANKTU[s] = tu_rel; RANKV[TKEYS[i]] = 0 }
    if (RANKV[TKEYS[i]] > maxrank) maxrank = RANKV[TKEYS[i]]
  }
  for (k = 0; k <= maxrank; k++) {
    ns = 0; split("", keysr); split("", ss); split("", protos)
    for (i = 1; i <= nt; i++) if (RANKV[TKEYS[i]] == k) {
      keysr[++ns] = TKEYS[i]
      split(TKEYS[i], parts, "\001"); ss[ns] = parts[1]; protos[parts[1]] = TESTP[TKEYS[i]]
    }
    judge_protos(tu_abs, protos, ss, ns)
    for (i = 1; i <= ns; i++) {
      split(keysr[i], parts, "\001"); s = parts[1]; sg = parts[2]
      verdict = PR[s]
      # spl paths sorted
      split("", sigs); for (j = 1; j <= TESTN[keysr[i]]; j++) sigs[j] = TESTSPL[keysr[i], j]
      msort(sigs, TESTN[keysr[i]])
      for (j = 1; j <= TESTN[keysr[i]]; j++) {
        if (verdict == "PASS") row(s, sg, sigs[j], tu_rel, "PASS", "compiles-with-prototype", "")
        else if (verdict == "FAIL") row(s, sg, sigs[j], tu_rel, "FAIL", "prototype-rejected", PRD[s])
        else row(s, sg, sigs[j], tu_rel, "UNTESTED", PRD[s], "")
      }
    }
  }
}
# sorted "sig\001path" list for a symbol (index records set)
function by_sorted(sym, out,    n, k) {
  split("", out); n = 0
  for (k = 1; k <= BSN[sym]; k++) out[++n] = BSV[sym, k]
  msort(out, n)
  return n
}
# text_extern_abi.spl: (ptr, len) split table -> SPLIT[sym SUBSEP idx]; sets TBL_ERR on malformed input
function text_split_table(root_unused,    n, i, L, src, line, out, j, owners, start, nown, endl, body, B, bn, cases, nm, p, s, rest, names, k, pos, idxs, ok, q1, q2, c, parts, nparts, matches, cur, seg, hit, hasdef, tmp, pathrel) {
  split("", SPLIT); TBL_ERR = ""
  pathrel = ABI_SPL
  n = fs_read(pathrel, L)
  if (n < 0) return
  # drop '#' comments outside "..." literals (line based; literals do not span lines)
  for (i = 1; i <= n; i++) L[i] = strip_hash(L[i])
  nown = 0
  for (i = 1; i <= n; i++) if (L[i] ~ /^(pub[ \t]+)?fn[ \t]+text_arg_indices([^A-Za-z0-9_]|$)/) { owners[++nown] = i }
  if (nown != 1) { TBL_ERR = pathrel ": expected one top-level text_arg_indices function, found " nown; return }
  start = owners[1]
  if (L[start] !~ /^(pub[ \t]+)?fn[ \t]+text_arg_indices[ \t]*\(.*\).*:[ \t]*$/) { TBL_ERR = pathrel ": malformed text_arg_indices declaration"; return }
  endl = start + 1
  while (endl <= n && (L[endl] ~ /^[[:space:]]*$/ || substr(L[endl], 1, 1) == " " || substr(L[endl], 1, 1) == "\t")) endl++
  bn = 0
  for (i = start + 1; i < endl; i++) B[++bn] = L[i]
  # body as one text with line start offsets
  body = ""; for (i = 1; i <= bn; i++) { BOFF[i] = length(body) + 1; body = body B[i] "\n" }
  nm = 0; split("", matches); split("", cases)
  for (i = 1; i <= bn; i++) {
    if (B[i] ~ /^[ \t]*case[ \t]+/ && B[i] !~ /^[ \t]*case[ \t]+_[ \t]*(\("[^"]*"\)[ \t]*)?:/) cases[i] = 1
    if (B[i] !~ /^[ \t]*case[[:space:]]/ && B[i] !~ /^[ \t]*case$/) continue
    if (text_case_at(substr(body, BOFF[i]))) { matches[i] = 1; TCN[i] = TC_N; for (j = 1; j <= TC_N; j++) { TCNAME[i, j] = TC_NAMES[j] } TCIDX[i] = TC_IDX }
  }
  hit = 0; for (i in matches) hit++
  ok = (hit > 0)
  for (i in matches) if (!(i in cases)) ok = 0
  for (i in cases) if (!(i in matches)) ok = 0
  if (!ok) { TBL_ERR = pathrel ": malformed text_arg_indices split cases"; return }
  for (i = 1; i <= bn; i++) if (i in matches) {
    # later cases override earlier ones
    for (j = 1; j <= TCN[i]; j++) {
      s = TCNAME[i, j]
      for (k in SPLIT) { if (startsw(k, s SUBSEP)) delete SPLIT[k] }
      nparts = split(TCIDX[i], parts, ",")
      for (k = 1; k <= nparts; k++) if (trim(parts[k]) != "") {
        if (trim(parts[k]) !~ /^[0-9]+$/) { TBL_ERR = pathrel ": malformed split index"; return }
        SPLIT[s SUBSEP (trim(parts[k]) + 0)] = 1
      }
    }
  }
}
function strip_hash(s,    out, k, j, ch, ok, n) {
  out = ""
  while (1) {
    # next " or #
    k = match(s, /["#]/)
    if (!k) return out s
    if (substr(s, RSTART, 1) == "#") return out substr(s, 1, RSTART - 1)
    k = RSTART; out = out substr(s, 1, k - 1)
    j = k + 1; ok = 0; n = length(s)
    while (j <= n) {
      ch = substr(s, j, 1)
      if (ch == "\\") { if (j < n) { j += 2; continue } break }
      if (ch == "\"") { ok = 1; break }
      j++
    }
    if (ok) { out = out substr(s, k, j - k + 1); s = substr(s, j + 1) }
    else { out = out "\""; s = substr(s, k + 1) }
  }
}
# TEXT_CASE at the start of s; fills TC_NAMES[1..TC_N], TC_IDX (raw text inside [ ])
function text_case_at(s,    p, c, names, nn, e, nm, t) {
  if (!match(s, /^[ \t]*case[[:space:]]+/)) return 0
  p = RLENGTH + 1; TC_N = 0; split("", TC_NAMES)
  while (substr(s, p, 1) == "\"") {
    e = index(substr(s, p + 1), "\"")
    if (!e) return 0
    nm = substr(s, p + 1, e - 1)
    if (index(nm, "\n")) return 0
    TC_NAMES[++TC_N] = nm
    p += e + 1
    match(substr(s, p), /^[[:space:]]*/); p += RLENGTH
    if (substr(s, p, 1) == "|") p++
    match(substr(s, p), /^[[:space:]]*/); p += RLENGTH
  }
  if (TC_N == 0 || substr(s, p, 1) != ":") return 0
  p++
  match(substr(s, p), /^[[:space:]]*/); p += RLENGTH
  if (substr(s, p, 6) != "return") return 0
  p += 6
  if (!match(substr(s, p), /^[[:space:]]+/)) return 0
  p += RLENGTH
  if (substr(s, p, 6) != "Some([") return 0
  p += 6
  if (!match(substr(s, p), /^[0-9,[:space:]]*\]\)/)) return 0
  TC_IDX = substr(s, p, RLENGTH - 2)
  return 1
}
function contract_check(    i, k, tu, n, symlist, nsym, ks, parts, t, rk) {
  hm_scan(); c_scan(0)
  split("", ALIAS); split("", NOM)
  spl_pass(1)
  for (k in ALIAS) if (k in NOM) { delete ALIAS[k]; delete NOM[k] }
  NREC = XN
  split("", BSN); split("", BSV); split("", BSSET); split("", BSYMS); nsym = 0
  for (i = 1; i <= XN; i++) {
    sym = XSYM[i]; sig = canonical_signature(XPAR[i], XRET[i])
    k = sym SUBSEP sig SUBSEP XPATH[i]
    if (k in BSSET) continue
    BSSET[k] = 1
    if (!(sym in BSN)) { BSN[sym] = 0; BSYMS[++nsym] = sym }
    BSN[sym]++; BSV[sym, BSN[sym]] = sig "\001" XPATH[i]
  }
  msort(BSYMS, nsym)
  text_split_table("")
  if (TBL_ERR != "") return 0
  RW = 0; split("", SYMRANK); split("", SYMRANKTU)
  for (i = 1; i <= NTU; i++) judge_tu(TUL[i], BSYMS, nsym)
  msort(RWK, RW)
  return 1
}
function contract_main(    i, r, t, line, rc, first, nrec, cp, cf, cu, hl, os_, arch, un, parts) {
  # host line
  rc = run_cc(CC " --version")
  first = (rc == 0 && trim(RC_T[1]) != "") ? trim(RC_T[1]) : "unavailable"
  if (rc == 0) { first = "unavailable"; for (i = 1; i <= RC_N; i++) if (trim(RC_T[i]) != "") { first = trim(RC_T[i]); break } }
  split(RT_UNAME, parts, " "); os_ = parts[1]; arch = parts[2]
  if (os_ ~ /^(MSYS|MINGW|CYGWIN)/) { os_ = "Windows"; if (arch == "x86_64") arch = "AMD64"; else if (arch == "aarch64") arch = "ARM64" }
  printf "RT_C_CONTRACT_HOST os=%s arch=%s cc=%s\n", os_, arch, first
  if (!contract_check()) { print "ERROR — " TBL_ERR; return 2 }
  for (i = 1; i <= RW; i++) {
    t = RWK[i]; sub(/^.*\001/, "", t); t = t + 0
    sg = RWsig[t]; gsub(/ /, "", sg)
    line = "RT_C_CONTRACT compile=" RWc[t] " symbol=" RWsym[t] " sig=" sg " spl=" RWspl[t] " tu=" RWtu[t] " reason=" RWr[t]
    if (RWd[t] != "") line = line " diag=" RWd[t]
    print line
    if (RWc[t] == "PASS") cp++; else if (RWc[t] == "FAIL") cf++; else cu++
  }
  printf "RT_C_CONTRACT_COMPILE tus=%d spl_records=%d rows=%d compile=PASS:%d/FAIL:%d/UNTESTED:%d link=UNTESTED\n", NTU, NREC, RW, cp + 0, cf + 0, cu + 0
  if (RW == 0) { print "ERROR — nothing was checked (0 rows)"; return 2 }
  return 0
}

# ---------------------------------------------------------------- init / main
function init_tables(    i, n, a) {
  HL[1] = "linux"; HL[2] = "macos"; HL[3] = "windows"; HL[4] = "freebsd"; HL[5] = "simpleos"
  HM["linux" SUBSEP "__linux__"] = 1; HM["linux" SUBSEP "__unix__"] = 1
  HM["macos" SUBSEP "__APPLE__"] = 1; HM["macos" SUBSEP "__MACH__"] = 1
  HM["windows" SUBSEP "_WIN32"] = 1; HM["windows" SUBSEP "_WIN64"] = 1
  HM["freebsd" SUBSEP "__FreeBSD__"] = 1; HM["freebsd" SUBSEP "__unix__"] = 1
  HM["simpleos" SUBSEP "__simpleos__"] = 1
  n = split("__linux__ __unix__ __APPLE__ __MACH__ _WIN32 _WIN64 __FreeBSD__ __simpleos__ __NetBSD__ __OpenBSD__", a, " ")
  for (i = 1; i <= n; i++) KNOWN[a[i]] = 1
  for (i = 1; i <= 4; i++) ISHOSTED[HL[i]] = 1
  SUFFIX["windows"] = "windows"; SUFFIX["win32"] = "windows"; SUFFIX["win"] = "windows"; SUFFIX["linux"] = "linux"
  SUFFIX["macos"] = "macos"; SUFFIX["darwin"] = "macos"; SUFFIX["freebsd"] = "freebsd"; SUFFIX["simpleos"] = "simpleos"
  TOPS[1] = "src/compiler"; TOPS[2] = "src/lib"; TOPS[3] = "src/app"; TOPS[4] = "src/os"
  n = split("i8 i16 i32 u8 u16 u32 bool f32 f64", a, " "); for (i = 1; i <= n; i++) NAR[a[i]] = 1
  RANK["unknown"] = 0; RANK["enforced"] = 1; RANK["seen"] = 2; RANK["nil"] = 3
  n = split("i8:int8_t i16:int16_t i32:int32_t i64:int64_t u8:uint8_t u16:uint16_t u32:uint32_t u64:uint64_t f32:float f64:double bool:bool", a, " ")
  for (i = 1; i <= n; i++) { split(a[i], SPLIT_, ":"); SCALAR[SPLIT_[1]] = SPLIT_[2] }
  HM_BASELINE = "scripts/check/rt_host_map_baseline.txt"
  PM_BASELINE = "scripts/check/rt_pointer_ref_map_baseline.txt"
  PP_BASELINE = "scripts/check/rt_param_ref_map_baseline.txt"
  PC_BASELINE = "scripts/check/rt_param_count_baseline.txt"
  ABI_SPL = "src/compiler/50.mir/text_extern_abi.spl"
  NULLP = "([(][A-Za-z0-9_ ]+[*]+[)][[:space:]]*)?(NULL|nullptr|0)"
  # NULLRET alternative 1 (a plain null return) and 2 (null arm of ?: expression)
  RE_NR1 = "[^A-Za-z0-9_]return[[:space:]]*[(]?[[:space:]]*" NULLP "[[:space:]]*[)]?[[:space:]]*;"
  RE_NR2 = "[^A-Za-z0-9_]return[^A-Za-z0-9_;][^;]*[?:][[:space:]]*" NULLP "[[:space:]]*[:;)]"
  RE_ENF = "^return[[:space:]]*([(][^()]*[)][[:space:]]*)?SIMPLE_RT_NONNULL[[:space:]]*[(]"
}
function run_selftest_host(    c, nm, want, i, got, body, ls, wi, cases) {
  body = "long rt_x(void) { return 1; }\n"
  C[1] = body; N[1] = "a.c"; W[1] = 0
  C[2] = "#if defined(__linux__)\n" body "#endif\n"; N[2] = "a.c"; W[2] = 1
  C[3] = "#ifdef _WIN32\n" body "#else\n" body "#endif\n"; N[3] = "a.c"; W[3] = 0
  C[4] = "#if defined(FEATURE_X)\n" body "#endif\n"; N[4] = "a.c"; W[4] = 0
  C[5] = body; N[5] = "a_windows.c"; W[5] = 1
  C[6] = body; N[6] = "windows/a.c"; W[6] = 1
  C[7] = "#if defined(__linux__)\n" body "#endif\n"; N[7] = "io_common.c"; W[7] = 1
  C[8] = body; N[8] = "startup/baremetal/a.c"; W[8] = 2
  C[9] = "#ifndef __APPLE__\nint y;\n#else\n" body "#endif\n"; N[9] = "a.c"; W[9] = 1
  C[10] = "#if defined(__linux__) || \\\n defined(__APPLE__)\n" body "#endif\n"; N[10] = "a.c"; W[10] = 1
  C[11] = "#if __linux__\n" body "#endif\n"; N[11] = "a.c"; W[11] = 1
  C[12] = "#if defined(__unix__)\n" body "#endif\n"; N[12] = "a.c"; W[12] = 1
  C[13] = "#if 0\n" body "#endif\n"; N[13] = "a.c"; W[13] = 2
  C[14] = "static long rt_x(void) { return 1; }\n"; N[14] = "a.c"; W[14] = 2
  for (i = 1; i <= 14; i++) {
    vf_reset()
    vf_put("src/runtime/" N[i], C[i])
    vf_put("src/lib/a.spl", "extern fn rt_x() -> i64\n")
    ROOT = ""
    SILENT = 1
    got = hm_run(0)
    SILENT = 0
    if (got != W[i]) { printf "ERROR — selftest case %d wanted %d got %d\n", i - 1, W[i], got; return 2 }
  }
  print "PASS — selftest 14 existing + include traversal cases"
  return 0
}
function incself(    pl, dl, hi, h, k, sym, want, wn, bad, w, nwant, vk, p) {
  hm_scan()
  for (hi = 1; hi <= 5; hi++) {
    h = HL[hi]; split("", want)
    want["rt_shared"] = 1; want["rt_leaf"] = 1; want["rt_unknown"] = 1; want["rt_public_inline"] = 1
    if (h == "linux") { want["rt_root_host"] = 1; want["rt_include_host"] = 1 }
    bad = 0
    for (k in want) { if (!((h ":" k) in PROV)) bad = 1; if (k != "rt_unknown" && !((h ":" k) in DEFN)) bad = 1 }
    for (k in PROV) if (substr(k, 1, length(h) + 1) == h ":" && !(substr(k, length(h) + 2) in want)) bad = 1
    for (k in DEFN) if (substr(k, 1, length(h) + 1) == h ":" && (!(substr(k, length(h) + 2) in want) || substr(k, length(h) + 2) == "rt_unknown")) bad = 1
    if (bad) {
      pl = ""; dl = ""
      for (k in PROV) if (substr(k, 1, length(h) + 1) == h ":") pl = pl " " substr(k, length(h) + 2)
      for (k in DEFN) if (substr(k, 1, length(h) + 1) == h ":") dl = dl " " substr(k, length(h) + 2)
      printf "ERROR — include selftest host %s possible=%s definite=%s\n", h, pl, dl
      return 2
    }
  }
  for (vk in VISIT) if (VISIT[vk] > 1) { print "ERROR — include selftest visited a cycle/diamond more than once"; return 2 }
  if (!(("linux" SUBSEP 0 SUBSEP FID["src/runtime/nested/leaf.h"]) in VISIT) || !("linux:rt_leaf" in PROV)) { print "ERROR — include selftest lost header definition provenance"; return 2 }
  print "PASS — include fixtures: definitions/static/prototypes/nested/conditions/cycles/diamonds/owned paths"
  return 0
}
# ---------------------------------------------------------------- pointer-map selftest (virtual tree)
function pt_tree(c, spl) { vf_reset(); vf_put("src/runtime/a.c", c); vf_put("src/lib/a.spl", spl) }
function pt_snull_codes(    k, seen, out, n, a, i) {
  split("", seen)
  for (k in SNULL) seen[SNULL[k]] = 1
  n = keys_sorted(seen, a); out = ""
  for (i = 1; i <= n; i++) out = out (i > 1 ? "," : "") a[i]
  return out
}
function pt_ret(idx, c, spl, want,    got) {
  pt_tree(c, spl); got = ptr_run(0, 0)
  if (got != want) { printf "ERROR — selftest case %d wanted %d got %d\n", idx, want, got; return 0 }
  return 1
}
function pt_enf(idx, c, spl, wc, we, wu,    got) {
  pt_tree(c, spl); got = ptr_run(0, 0)
  if (got != wc || P_ENF != we || P_UNK != wu) {
    printf "ERROR — enforced selftest case %d wanted exit=%d enforced=%d UNKNOWN=%d, got exit=%d enforced=%d UNKNOWN=%d\n", idx, wc, we, wu, got, P_ENF, P_UNK
    return 0
  }
  return 1
}
function pt_par(idx, c, spl, wc, wsrt, wnar, wsn, wunp,    got, codes, nsrt) {
  if (wsrt > 0) wc = 1
  pt_tree(c, spl); got = ptr_run(0, 0)
  codes = pt_snull_codes(); nsrt = set_count(SRT003)
  if (got != wc || nsrt != wsrt || set_count(PNARROW) != wnar || codes != wsn || P_UNPARSED() != wunp) {
    printf "ERROR — param selftest case %d wanted exit=%d srt003=%d narrow=%d snull='%s' unparsed=%d, got exit=%d srt003=%d narrow=%d snull='%s' unparsed=%d\n", idx, wc, wsrt, wnar, wsn, wunp, got, nsrt, set_count(PNARROW), codes, P_UNPARSED()
    return 0
  }
  return 1
}
function P_UNPARSED() { return set_count(PUNP) }
function run_selftest_ptr(    nilc, okc, enf, i, t, n_ret, n_enf, n_par, got, brow, held) {
  nilc = "char *rt_x(void) {\n  if (a) return NULL;\n  return b;\n}\n"
  okc = "char *rt_x(void) {\n  return b;\n}\n"
  n_ret = 15; n_enf = 8; n_par = 28
  if (!pt_ret(0, "__attribute__((visibility(\"default\"))) char *rt_x(void) { return NULL; }\n", "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(1, "__attribute__((weak)) char *rt_x(void) { return NULL; }\n", "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(2, nilc, "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(3, nilc, "extern fn rt_x() -> text?\n", 0)) return 2
  if (!pt_ret(4, okc, "extern fn rt_x() -> text\n", 0)) return 2
  if (!pt_ret(5, okc, "extern fn rt_x() -> i32\n", 1)) return 2
  if (!pt_ret(6, "char *rt_x(void);\n", "extern fn rt_x() -> text\n", 0)) return 2
  if (!pt_ret(7, "static char *rt_x(void) { return NULL; }\n", "extern fn rt_x() -> text\n", 2)) return 2
  if (!pt_ret(8, nilc, "fn other() -> text\n", 2)) return 2
  if (!pt_ret(9, okc, "extern fn rt_x() -> i32?\n", 1)) return 2
  if (!pt_ret(10, "char *rt_x(void) {\n  if (c == '}') y();\n  return NULL;\n}\n", "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(11, "char *rt_x(void) {\n  return p ? p : NULL;\n}\n", "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(12, "char *rt_x(void) {\n  return bad ? NULL : p;\n}\n", "extern fn rt_x() -> text\n", 1)) return 2
  if (!pt_ret(13, nilc, "extern fn rt_x<T>(v: T) -> [T]\n", 1)) return 2
  if (!pt_ret(14, nilc, "extern fn rt_x(cb: fn(i64) -> i64) -> text\n", 1)) return 2
  enf = "char *rt_x(void) {\n  return SIMPLE_RT_NONNULL(\"rt_x\", b);\n}\n"
  if (!pt_enf(0, enf, "extern fn rt_x() -> text\n", 0, 1, 0)) return 2
  if (!pt_enf(1, enf, "extern fn rt_x() -> text?\n", 0, 0, 0)) return 2
  if (!pt_enf(2, "char *rt_x(void) {\n  return (char *)SIMPLE_RT_NONNULL(\"rt_x\", b);\n}\n", "extern fn rt_x() -> text\n", 0, 1, 0)) return 2
  if (!pt_enf(3, "char *rt_x(void) {\n  if (a) return NULL;\n  return SIMPLE_RT_NONNULL(\"rt_x\", b);\n}\n", "extern fn rt_x() -> text\n", 1, 0, 0)) return 2
  if (!pt_enf(4, "char *rt_x(void) {\n  return p ? SIMPLE_RT_NONNULL(\"rt_x\", p) : NULL;\n}\n", "extern fn rt_x() -> text\n", 1, 0, 0)) return 2
  if (!pt_enf(5, "char *rt_x(void) {\n  if (a) return SIMPLE_RT_NONNULL(\"rt_x\", p);\n  return b;\n}\n", "extern fn rt_x() -> text\n", 0, 0, 1)) return 2
  if (!pt_enf(6, "char *rt_x(void);\n", "extern fn rt_x() -> text\n", 0, 0, 1)) return 2
  if (!pt_enf(7, enf "char *rt_x(void) {\n  return b;\n}\n", "extern fn rt_x() -> text\n", 0, 0, 1)) return 2
  i = 0
  if (!pt_par(i++, "char *rt_x(char *a, void *d) { return b; }\n", "extern fn rt_x(a: text?, d: Dict<text, i64>) -> text\n", 1, 0, 0, "SNULL002", 0)) return 2
  if (!pt_par(i++, "char *rt_x(int64_t h, int64_t size, const char *p);\n", "extern fn rt_x(h: i64, p: text?) -> text\n", 1, 1, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: Option<text>) -> text\n", 1, 0, 0, "SNULL002", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: text? = nil) -> text\n", 1, 0, 0, "SNULL002", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a, int64_t b);\n", "extern fn rt_x(a: text) -> text\n", 0, 1, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: i32) -> text\n", 1, 0, 1, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: text?) -> text\n", 1, 0, 0, "SNULL002", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: &text) -> text\n", 1, 0, 0, "SNULL003", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: &mut [u8]) -> text\n", 1, 0, 0, "SNULL003", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(char *a, ...);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(void);\n", "extern fn rt_x() -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(int64_t n);\n", "extern fn rt_x(n: i64) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(int (*cb)(void *));\n", "extern fn rt_x(cb: text) -> text\n", 0, 0, 0, "", 1)) return 2
  if (!pt_par(i++, "char *rt_x(char *a);\n", "extern fn rt_x(a) -> text\n", 0, 0, 0, "", 1)) return 2
  if (!pt_par(i++, "char *rt_x(char *a,\n  uint64_t n);\n", "extern fn rt_x(a: text, n: i64) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *p, uint64_t p_len);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(int64_t n, uint64_t len);\n", "extern fn rt_x(n: i64) -> text\n", 0, 1, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *p, uint64_t p_len);\n", "extern fn rt_x(p: i64, n: i64) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *p, uint64_t p_len, uint64_t extra);\n", "extern fn rt_x(a: text) -> text\n", 0, 1, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *p, int64_t n);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *k, int64_t kl, const uint8_t *d, int64_t dl);\n", "extern fn rt_x(a: text, b: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const char *s, int64_t count);\n", "extern fn rt_x(a: text) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "int64_t rt_x(const char *path, int64_t n);\nchar *rt_y(void) {\n return b;\n}\n", "extern fn rt_x(path: text) -> i64\nextern fn rt_y() -> text\n", 1, 1, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const uint8_t *p, uint64_t p_len, int64_t count);\n", "extern fn rt_x(a: text, n: i64) -> text\n", 0, 0, 0, "", 0)) return 2
  if (!pt_par(i++, "char *rt_x(const int32_t *p, int64_t count);\n", "extern fn rt_x(a: text) -> text\n", 0, 1, 0, "", 0)) return 2
  # param baseline: absent fails, regen holds, stale row fails
  pt_tree("char *rt_x(char *a);\n", "extern fn rt_x(a: text?) -> text\n")
  if (ptr_run(0, 0) != 1) { print "ERROR — selftest param baseline absent should fail"; return 2 }
  if (ptr_run(0, 1) != 0 || ptr_run(0, 0) != 0) { print "ERROR — selftest param regen did not hold its row"; return 2 }
  VF[PP_BASELINE] = VF[PP_BASELINE] "src/lib/a.spl:rt_gone:0:text?\n"
  if (ptr_run(0, 0) != 1) { print "ERROR — selftest stale param row should fail"; return 2 }
  pt_tree(nilc, "extern fn rt_x() -> text\n")
  brow = "src/lib/a.spl:rt_x:text\n"
  VF[PM_BASELINE] = brow
  held = ptr_run(0, 0)
  VF[PM_BASELINE] = brow "src/lib/a.spl:rt_y:text\n"
  if (held != 0 || ptr_run(0, 0) != 1) { print "ERROR — selftest baseline held/stale"; return 2 }
  printf "PASS — selftest %d return, %d enforced, %d parameter cases\n", n_ret, n_enf, i
  return 0
}
# ---------------------------------------------------------------- rt-binding-index selftest (virtual tree)
function ix_tree(c, spl) { vf_reset(); vf_put("src/runtime/a.c", c); vf_put("src/lib/a.spl", spl) }
function ix_find(sym,    i) { for (i = 1; i <= XN; i++) if (XSYM[i] == sym) return i; return 0 }
function run_selftest_index(    runtime_c, spl, nf, first, second, r, sym, mv, pv, want_m, want_p, syms, i, n, id_ok, id_ok_i, id_nil, id_ok_changed, id_nil_changed, spl2, ok_id) {
  runtime_c = "char *rt_ok(void) {\n  return SIMPLE_RT_NONNULL(b);\n}\n" \
    "char *rt_nil(void) {\n  if (a) return NULL;\n  return b;\n}\n" \
    "#if defined(__linux__)\nlong rt_linux_only(void) { return 1; }\n#endif\n" \
    "#ifdef SOME_FEATURE_X\nlong rt_feature_gated(void) { return 1; }\n#endif\n"
  spl = "extern fn rt_ok() -> text\nextern fn rt_nil() -> text\nextern fn rt_linux_only() -> i64\nextern fn rt_feature_gated() -> i64\nextern fn rt_missing(x: i64) -> i64\n"
  nf = 0
  ix_tree(runtime_c, spl); index_build(0); index_render(); first = jd_text()
  ix_tree(runtime_c, spl); index_build(0); index_render(); second = jd_text()
  if (first != second) FAILS[++nf] = "two runs differ"
  n = split("rt_ok:PASS:PASS rt_nil:PASS:FAIL rt_linux_only:FAIL:UNKNOWN rt_feature_gated:UNKNOWN:UNKNOWN rt_missing:UNKNOWN:UNKNOWN", syms, " ")
  ix_tree(runtime_c, spl); index_build(0)
  for (i = 1; i <= n; i++) {
    split(syms[i], want_m, ":"); sym = want_m[1]; r = ix_find(sym)
    if (!r) { FAILS[++nf] = "missing record " sym; continue }
    if (XMV[r] != want_m[2] || XPV[r] != want_m[3]) FAILS[++nf] = sprintf("%s map=%s pointer=%s, wanted %s %s", sym, XMV[r], XPV[r], want_m[2], want_m[3])
  }
  r = ix_find("rt_feature_gated")
  if (r) {
    if (XMR[r] != "conditional-provider-on-hosted-profile") FAILS[++nf] = "rt_feature_gated map reason is " XMR[r] ", wanted conditional-provider-on-hosted-profile"
    if (XST[r, 1] != "conditional" || XST[r, 3] != "conditional") FAILS[++nf] = "rt_feature_gated provider states are not conditional on hosted profiles"
  }
  r = ix_find("rt_nil")
  if (!r || XPR[r] != "nil-mismatch") FAILS[++nf] = "rt_nil pointer reason is not nil-mismatch"
  for (i = 1; i <= XN; i++) if (XST[i, 5] != "unknown") FAILS[++nf] = "simpleos row not unknown on " XSYM[i]
  ok_id = sha256_16("rt_ok\n" XSIG[ix_find("rt_ok")]); id_nil = sha256_16("rt_nil\n" XSIG[ix_find("rt_nil")])
  if (length(ok_id) != 16) FAILS[++nf] = "interface id is not 16 hex characters"
  spl2 = spl; sub(/extern fn rt_ok\(\) -> text/, "extern fn rt_ok() -> i64", spl2)
  ix_tree(runtime_c, spl2); index_build(0)
  if (sha256_16("rt_ok\n" XSIG[ix_find("rt_ok")]) == ok_id) FAILS[++nf] = "interface id did not change with the signature"
  if (sha256_16("rt_nil\n" XSIG[ix_find("rt_nil")]) != id_nil) FAILS[++nf] = "interface id changed for an unchanged signature"
  if (nf) {
    for (i = 1; i <= nf; i++) print "SELFTEST FAIL: " FAILS[i]
    printf "ERROR — selftest %d failure(s)\n", nf
    return 1
  }
  print "PASS — selftest 5 records, #ifdef conditional provider is UNKNOWN, 2 runs byte-identical, simpleos unknown, compile/link UNTESTED"
  return 0
}
function default_tus(    i, n, rel, names, nn, L, k, j) {
  NTU = 0; TUL[++NTU] = "src/runtime/runtime_simd_dispatch.c"
  nn = 0
  for (i = 1; i <= FN; i++) {
    rel = FL[i]
    if (substr(rel, 1, 12) == "src/runtime/" && endsw(rel, ".c") && index(substr(rel, 13), "/") == 0 && rel != TUL[1]) names[++nn] = rel
  }
  msort(names, nn)
  for (k = 1; k <= nn; k++) {
    n = fs_read(names[k], L)
    for (j = 1; j <= n; j++) if (L[j] ~ /#[[:space:]]*include[[:space:]]*"runtime_nonnull[.]h"/) { TUL[++NTU] = names[k]; break }
  }
}
function contract_begin(    n, i, t) {
  CC = ENVIRON["RT_CC"]; TMPD = ENVIRON["RT_TMP"]; CCTO = ENVIRON["RT_TIMEOUT"]
  if (CCTO != "") CCTO = CCTO " "
  RT_UNAME = ENVIRON["RT_UNAME"]
  fs_list_load()
  t = ENVIRON["RT_TUS"]
  if (t == "") default_tus()
  else { n = split(t, TMPA, "\n"); NTU = 0; for (i = 1; i <= n; i++) if (TMPA[i] != "") TUL[++NTU] = TMPA[i] }
  return contract_main()
}
BEGIN {
  init_tables()
  ROOT = ENVIRON["RT_ROOT"]; VIRT = 0
  OUTP_ = ENVIRON["RT_OUT"]
  rc = 0
  if (SELFTEST && MODE == "host") rc = run_selftest_host()
  else if (SELFTEST && MODE == "ptr") rc = run_selftest_ptr()
  else if (SELFTEST && MODE == "index") rc = run_selftest_index()
  else if (INCSELF) { fs_list_load(); rc = incself() }
  else if (MODE == "contract") rc = contract_begin()
  else {
    fs_list_load()
    if (MODE == "host") rc = hm_run(REGEN + 0)
    else if (MODE == "ptr") rc = ptr_run(REGEN + 0, REGEN_PARAM + 0)
    else if (MODE == "index") rc = index_main()
  }
  exit rc
}
