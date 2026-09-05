# Header-scoped signature-type import-provenance predicate, AUTO mode.
#
# Single awk process (the file list is read by awk itself, never by xargs --
# xargs splits on ARG_MAX and each split would build its OWN declaration map,
# silently producing per-batch answers that look plausible and are wrong).
#
# Pass 1 builds name -> declaring module over the whole tree; a name declared in
# more than one module is AMBIGUOUS and is excluded from the automated verdict.
# Pass 2 reports files that name a uniquely-declared type in annotation position
# without a real header-scoped import for it.
function modname(p,   parts,k,i,seg,out) {
  sub(/^\.\//,"",p); sub(/\.spl$/,"",p)
  k=split(p,parts,"/"); out=""
  for (i=2;i<=k;i++) { seg=parts[i]; sub(/^[0-9]+\./,"",seg); out=(out==""?seg:out "." seg) }
  sub(/^lib\./,"std.",out)
  return out
}
function scanfile(f, pass,   line,n,t,s,ob,cb,instr,cont,buf,cls,d,nm,i,ntok,tok) {
  instr=0; cont=0; buf=""
  while ((getline line < f) > 0) {
    n=0; t=line
    while (index(t,"\"\"\"")>0) { n++; t=substr(t,index(t,"\"\"\"")+3) }
    if (instr) { if (n%2==1) instr=0; continue }
    s=line; sub(/^[ \t]+/,"",s); sub(/[ \t]+$/,"",s)
    cls=""
    if (cont) {
      buf=buf " " s
      if (index(s,"}")>0) { cls="use"; s=buf; cont=0 }
      if (n%2==1) instr=1
      if (cls=="") continue
    } else if (substr(s,1,1)=="#") { if (n%2==1) instr=1; continue }
    else if (s ~ /^use / || s ~ /^export use / || s ~ /^export /) {
      ob=0; t=s; while (index(t,"{")>0) { ob++; t=substr(t,index(t,"{")+1) }
      cb=0; t=s; while (index(t,"}")>0) { cb++; t=substr(t,index(t,"}")+1) }
      if (ob>cb) { buf=s; cont=1; if (n%2==1) instr=1; continue }
      cls="use"; if (n%2==1) instr=1
    } else { cls="code"; if (n%2==1) instr=1 }

    if (cls=="use") {
      if (pass==2) { ntok=split(s,tok,/[^A-Za-z0-9_]+/); for (i=1;i<=ntok;i++) if (tok[i]!="") used[tok[i]]=1 }
      continue
    }
    # code line
    if (match(line,/^(struct|class|enum|trait)[ \t]+[A-Z][A-Za-z0-9_]*/)) {
      d=substr(line,RSTART,RLENGTH); sub(/^[a-z]+[ \t]+/,"",d)
      if (pass==1) { if (!((f SUBSEP d) in owndecl)) { owndecl[f SUBSEP d]=1; if (!(d in declmod)) { declmod[d]=modname(f); declcount[d]=1 } else if (declmod[d]!=modname(f)) declcount[d]++ } }
      else own[d]=1
    }
    if (pass==2) {
      t=line
      while (match(t,/[:\[<,(][ \t]*[A-Z][A-Za-z0-9_]*/)) {
        nm=substr(t,RSTART,RLENGTH); sub(/^[:\[<,(][ \t]*/,"",nm)
        pos[nm]=1
        t=substr(t,RSTART+RLENGTH)
      }
    }
  }
  close(f)
}
BEGIN {
  while ((getline line < EXCL) > 0) { gsub(/[ \t\r]/,"",line); if (line!="" && substr(line,1,1)!="#") excl[line]=1 }
  close(EXCL)
  nf=0
  while ((getline line < LIST) > 0) { if (line!="") flist[++nf]=line }
  close(LIST)
  for (i=1;i<=nf;i++) scanfile(flist[i],1)
  nof=0; namb=0
  for (d in declcount) if (declcount[d]>1) { namb++; print d "\t" declmod[d] > AMBOUT }
  for (i=1;i<=nf;i++) {
    delete used; delete pos; delete own
    scanfile(flist[i],2)
    m=modname(flist[i])
    for (T in pos) {
      if (T in excl) continue
      if (length(T)<=2 && T==toupper(T)) continue
      if (!(T in declcount) || declcount[T]!=1) continue
      if (T in own) continue
      if (declmod[T]==m) continue
      if (T in used) continue
      print flist[i] "\t" T "\t" declmod[T]
      nof++
    }
  }
  printf "META files=%d decls=%d ambiguous=%d offenders=%d\n", nf, length(declcount), namb, nof > "/dev/stderr"
}
