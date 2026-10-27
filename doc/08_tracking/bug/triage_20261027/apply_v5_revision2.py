#!/usr/bin/env python3
"""One-off append-only V5 revision migration; no product DB parser/serializer."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import os
import re
import subprocess
import sys
import tempfile
import time
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DB = ROOT / "doc/08_tracking/bug/bug_db.sdn"
TRIAGE = ROOT / "doc/08_tracking/bug/triage_20261027"
V4C = TRIAGE / "reviewed_categories_v4.sdn"
V4R = TRIAGE / "residual_ids_v4.sdn"
V5C = TRIAGE / "reviewed_categories_v5.sdn"
V5R = TRIAGE / "residual_ids_v5.sdn"
MANIFEST = TRIAGE / "manifest_v5.sdn"
OVERLAY = TRIAGE / "evidence_v5/adjudication_overlay_v2.csv"
DETAIL = TRIAGE / "evidence_v5/residual31_revision2.md"
RECEIPT = TRIAGE / "application_receipt_v5_revision2.sdn"
CAMPAIGN = "triage-20261027-v5-revision2"
REVISION = "2"
ASSESS = "c0b3ad911f4cb00c0f3550b05baa8d06347d17d0"
BASE = "d83d1661c4fc02c0d6d7cbc027821a2e15416007"
EVIDENCE_COMMIT = BASE
BASE_DB_SHA = "ac02c7dc8a3e4176c79281c411cac47f82ca79ee39540858e768d5d2671d1d43"
V4_CAT_SHA = "f47867ce23862fe32ca679bd72a0f53a2ea1e0727044f8c32f71209653d4da42"
V4_RES_SHA = "632c63f649780004373b3713f8e8ce4f5e91196974e9cd5a0b22e89d1d49e007"
V5_CAT_SHA = "5d18ffdcdd46158189c884eeec341174b4fa5a96251c764aa48800b18b0d11e7"
V5_RES_SHA = "08150ce70e107a74a151e0a73f5cb35412614c7cc2ac428d3ecb219dcca9453a"
MANIFEST_SHA = "b60c4eaadba3938a369491a4cabda36911cedc7ba140ceddf6a99d77a4d8ca7b"
OVERLAY_SHA = "f8ade51a2b003e8d2dc3f7ffd7867201a6ff33367fec784982b51f5e46f6a0b2"
DETAIL_SHA = "4b3c281d694cabdc6283ed792d0a3b79ccaba4738bbda9cf2525a9f16df9bfaa"
V4_CAMPAIGN = "triage-20261027-v4"
MAX_LINE = 1152921504606846975
MAX_PAYLOAD = 1536
KEY = re.compile(rb"^[A-Za-z0-9_./:=+-]+(?: [A-Za-z0-9_./:=+-]+)*$")
HEADER = re.compile(rb"^[A-Za-z_][A-Za-z0-9_-]* \|.*\|$")
ROW_ID = re.compile(rb"^\s*([^,|\"\s]+),")
LOG_PREFIX = re.compile(rb"^\s*([^,|\"\s]+),\s*(-?[0-9]+),")
OVERLAY_FIELDS = ("bug_id", "assessed_sha", "validity", "reproducibility", "solution", "structural_change", "inspection_level", "recommended_action", "review_state", "evidence_refs", "rationale", "raw_corrections")
CATEGORY_FIELDS = ("bug_id", "assessed_sha", "inspection_level", "validity", "reproducibility", "solution", "structural_change", "action", "review_receipt")
PAYLOAD_ORDER = ("audit", "revision", "assessed_sha", "review", "inspection", "validity", "reproducibility", "scope", "solution", "structural", "action", "review_receipt", "evidence", "evidence_sha256", "manifest_sha256", "evidence_commit", "supersedes_sha256", "overlay_row_sha256")

def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def committed(path: Path) -> bytes:
    return subprocess.run(["git", "show", f"{BASE}:{path.relative_to(ROOT).as_posix()}"], cwd=ROOT, check=True, capture_output=True).stdout

def sdn(path: Path, fields: int) -> list[list[str]]:
    result = []
    for line in path.read_bytes().splitlines():
        if not line.strip() or line.lstrip().startswith(b"#") or b"|" in line:
            continue
        row = [v.strip().decode("ascii") for v in line.split(b",")]
        if len(row) != fields:
            raise ValueError(f"{path}: expected {fields} cells, got {len(row)}")
        result.append(row)
    return result

def check_inputs():
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, text=True, capture_output=True).stdout.strip()
    if head != BASE:
        raise ValueError(f"fixed-base one-off refuses HEAD={head}, expected {BASE}")
    pins = ((V4C,V4_CAT_SHA),(V4R,V4_RES_SHA),(V5C,V5_CAT_SHA),(V5R,V5_RES_SHA),(MANIFEST,MANIFEST_SHA),(OVERLAY,OVERLAY_SHA),(DETAIL,DETAIL_SHA))
    for p, expected in pins:
        raw = p.read_bytes()
        if sha(raw) != expected or committed(p) != raw:
            raise ValueError(f"input differs from frozen committed blob: {p}")
    v4c = {r[0]: dict(zip(CATEGORY_FIELDS,r)) for r in sdn(V4C,9)}
    v4rrows = sdn(V4R,10)
    v4r = {r[0]: dict(zip((*CATEGORY_FIELDS[:-1],"action","review_state","review_receipt"),r)) for r in v4rrows}
    # V4 residual schema: id,assessment,inspection,validity,repro,solution,structural,action,review,receipt.
    v4r = {r[0]: {"bug_id":r[0],"assessed_sha":r[1],"inspection_level":r[2],"validity":r[3],"reproducibility":r[4],"solution":r[5],"structural_change":r[6],"action":r[7],"review_state":r[8],"review_receipt":r[9]} for r in v4rrows}
    c5 = {r[0]: dict(zip(CATEGORY_FIELDS,r)) for r in sdn(V5C,9)}
    r5rows = sdn(V5R,9)
    r5 = {r[0]: {"bug_id":r[0],"assessed_sha":r[1],"inspection_level":r[2],"validity":r[3],"reproducibility":r[4],"solution":r[5],"structural_change":r[6],"action":r[7],"review_receipt":r[8],"review_state":"needs_more_evidence"} for r in r5rows}
    if len(v4c)!=1571 or len(v4r)!=31 or len(c5)!=1577 or len(r5)!=25:
        raise ValueError("unexpected V4/V5 category partition counts")
    if set(v4c)&set(v4r) or set(c5)&set(r5) or len(c5)+len(r5)!=1602:
        raise ValueError("category partitions overlap or do not cover 1602 IDs")
    if any(c5.get(bug) != row for bug,row in v4c.items()):
        raise ValueError("a prior V4 accepted category field changed in V5")
    if any(x["assessed_sha"] != ASSESS for x in (*v4c.values(),*v4r.values(),*c5.values(),*r5.values())):
        raise ValueError("mixed assessment digest")
    overlay_bytes=OVERLAY.read_bytes()
    lines=overlay_bytes.splitlines(keepends=True)
    if any(not line.endswith(b"\n") for line in lines):
        raise ValueError("overlay CSV must use LF-terminated physical records")
    parsed=[]
    for line in lines[1:]:
        cells=next(csv.reader([line.decode("utf-8").rstrip("\n")]))
        if len(cells)!=12:
            raise ValueError("overlay row field count changed")
        parsed.append((dict(zip(OVERLAY_FIELDS,cells)),line))
    overlay={row["bug_id"]:(row,raw) for row,raw in parsed}
    if len(overlay)!=31 or set(overlay)!=set(v4r):
        raise ValueError("overlay IDs do not exactly equal V4 residual IDs")
    if set(v4c).issubset(c5) is False or set(r5)-set(v4r):
        raise ValueError("V5 does not preserve prior accepted partition or residual subset")
    accepted_delta=set(c5)-set(v4c)
    if accepted_delta != set(v4r)-set(r5) or len(accepted_delta)!=6:
        raise ValueError("six V4 residual admissions do not match V5 delta")
    for bug, (o, raw) in overlay.items():
        final = c5.get(bug) or r5.get(bug)
        mapping={"assessed_sha":"assessed_sha","validity":"validity","reproducibility":"reproducibility","solution":"solution","structural_change":"structural_change","inspection_level":"inspection_level","recommended_action":"action"}
        if any(o[a] != final[b] for a,b in mapping.items()):
            raise ValueError(f"overlay fields differ from committed V5 category: {bug}")
        if o["review_state"] != ("accepted" if bug in c5 else "needs_more_evidence"):
            raise ValueError(f"overlay review state differs from V5 partition: {bug}")
        if o["reproducibility"] != "untested":
            raise ValueError(f"unexpected reproduction claim: {bug}")
    return {**c5,**r5}, set(r5), v4r, overlay, {"v4_categories":V4_CAT_SHA,"v4_residual":V4_RES_SHA,"v5_categories":V5_CAT_SHA,"v5_residual":V5_RES_SHA,"manifest":MANIFEST_SHA,"overlay":OVERLAY_SHA,"detail":DETAIL_SHA}

def tables(data: bytes):
    heads=[]; off=0
    for line in data.splitlines(keepends=True):
        clean=line.rstrip(b"\r\n")
        if HEADER.match(clean): heads.append((off,clean.split(b" |",1)[0].decode("ascii")))
        off+=len(line)
    if len([x for x in heads if x[1]=="bug_investigation_logs"])!=1:
        raise ValueError("exactly one investigation log section required")
    sections={}
    for i,(start,name) in enumerate(heads):
        end=heads[i+1][0] if i+1<len(heads) else len(data)
        h_end=data.find(b"\n",start)
        if h_end<0: raise ValueError("unterminated table header")
        pos=h_end+1; rows=[]
        while pos<end:
            e=data.find(b"\n",pos); e=len(data) if e<0 else e+1
            row=data[pos:e]
            if row.strip(): rows.append((pos,e,row))
            pos=e
        sections[name]=rows
    schema=b"bug_investigation_logs |bug_id, line_num, content|"
    if [l.rstrip(b"\r\n") for l in data.splitlines(keepends=True) if l.startswith(b"bug_investigation_logs ")] != [schema]:
        raise ValueError("investigation log schema mismatch")
    rows=sections["bug_investigation_logs"]
    insert_at=rows[-1][1] if rows else data.find(b"\n",next(x[0] for x in heads if x[1]=="bug_investigation_logs"))+1
    return sections, insert_at

def parse_payload(raw: bytes) -> dict[str,str]:
    try: text=raw.decode("ascii").strip()
    except UnicodeDecodeError as e: raise ValueError("non-ASCII log payload") from e
    out={}
    for cell in text.split(" "):
        if "=" not in cell: raise ValueError("invalid key-value payload")
        k,v=cell.split("=",1)
        if k in out or not v: raise ValueError("duplicate or empty payload field")
        out[k]=v
    return out

def semantic_digest(bug_id: str, fields: dict[str,str]) -> str:
    material=[f"bug_id={bug_id}"]+[f"{k}={fields[k]}" for k in PAYLOAD_ORDER]
    return sha("\n".join(material).encode("ascii"))

def v4_digest(bug_id: str, fields: dict[str,str]) -> str:
    keys=("audit","assessed_sha","review","inspection","validity","reproducibility","scope","solution","structural","action","review_receipt","evidence","evidence_sha256","manifest_sha256","evidence_commit","scope_evidence","scope_sha256")
    material=[fields["audit"],bug_id]+[fields[k] for k in keys[1:]]
    return sha("\n".join(material).encode("ascii"))

def crc(data: bytes) -> int:
    if not data.startswith(b"#sdn-crc32:") or b"\n" not in data: raise ValueError("missing SDN CRC header")
    end=data.index(b"\n"); expected=int(data[len(b"#sdn-crc32:"):end]); actual=zlib.crc32(data[end+1:])&0xffffffff
    if expected!=actual: raise ValueError(f"CRC mismatch: {expected} != {actual}")
    return expected

def reseal(data: bytes) -> tuple[bytes,int]:
    end=data.index(b"\n"); body=data[end+1:]; value=zlib.crc32(body)&0xffffffff
    return f"#sdn-crc32:{value}\n".encode()+body,value

def prior_records(data: bytes, ids: set[str], v4r: dict, overlay: dict):
    sections,_=tables(data)
    active={i:[] for i in ids}
    for table in ("bugs_active","bugs"):
        for _,_,row in sections.get(table,[]):
            m=ROW_ID.match(row)
            if m and m.group(1).decode("ascii") in active: active[m.group(1).decode("ascii")].append(row)
    missing=[i for i,rows in active.items() if not rows]
    if missing: raise ValueError(f"V5 target missing from active/archive rows: {missing[:3]}")
    logs=[]
    for _,_,row in sections["bug_investigation_logs"]:
        m=LOG_PREFIX.match(row)
        if not m: continue
        bug=m.group(1).decode("ascii"); num=int(m.group(2)); payload=row[m.end():].strip()
        if bug in ids:
            fields=parse_payload(payload)
            if fields.get("audit")==V4_CAMPAIGN:
                logs.append((bug,num,row,fields))
            elif fields.get("audit")==CAMPAIGN:
                logs.append((bug,num,row,fields))
            else:
                raise ValueError(f"unrelated later campaign exists for target; requires adjudication: {bug}")
    by_id={i:[] for i in ids}
    for x in logs: by_id[x[0]].append(x)
    old={}
    for bug in ids:
        prior=[x for x in by_id[bug] if x[3].get("audit")==V4_CAMPAIGN]
        revision=[x for x in by_id[bug] if x[3].get("audit")==CAMPAIGN]
        if len(prior)!=1: raise ValueError(f"expected exactly one V4 semantic note for {bug}, got {len(prior)}")
        _,_,row,fields=prior[0]
        if fields.get("record_sha256")!=v4_digest(bug,fields): raise ValueError(f"V4 record semantic digest invalid: {bug}")
        exp=v4r[bug]; ov=overlay[bug][0]
        if fields.get("assessed_sha")!=ASSESS or fields.get("review")!="needs_more_evidence" or fields.get("inspection")!=exp["inspection_level"] or fields.get("validity")!=exp["validity"] or fields.get("reproducibility")!="untested" or fields.get("solution")!=exp["solution"] or fields.get("structural")!=exp["structural_change"] or fields.get("action")!=exp["action"]:
            raise ValueError(f"V4 note semantics differ from expected prior residual: {bug}")
        if revision and len(revision)>1: raise ValueError(f"multiple V5 revision rows: {bug}")
        old[bug]=(row,fields["record_sha256"],prior[0][1],revision)
    return sections,old

def new_fields(bug: str, cat: dict, pending: bool, prior_sha: str, overlay: dict, raw_overlay: bytes, digests: dict):
    f={"audit":CAMPAIGN,"revision":REVISION,"assessed_sha":ASSESS,"review":"needs_more_evidence" if pending else "accepted","inspection":cat["inspection_level"],"validity":cat["validity"],"reproducibility":"untested","scope":"UNRUN","solution":cat["solution"],"structural":cat["structural_change"],"action":cat["action"],"review_receipt":cat["review_receipt"],"evidence":"doc/08_tracking/bug/triage_20261027/evidence_v5/residual31_revision2.md","evidence_sha256":digests["detail"],"manifest_sha256":digests["manifest"],"evidence_commit":EVIDENCE_COMMIT,"supersedes_sha256":prior_sha,"overlay_row_sha256":sha(raw_overlay)}
    digest=semantic_digest(bug,f)
    payload=" ".join([f"{k}={f[k]}" for k in PAYLOAD_ORDER]+[f"record_sha256={digest}"]).encode("ascii")
    if len(payload)>MAX_PAYLOAD or not KEY.fullmatch(payload): raise ValueError(f"unsafe or oversize payload for {bug}: {len(payload)} bytes")
    return payload,digest,f

def plan(data: bytes, categories: dict, pending: set, v4r: dict, overlay: dict, digests: dict, expected_sha: str|None=None):
    actual=sha(data)
    if expected_sha and actual!=expected_sha: raise ValueError(f"stale database CAS: expected {expected_sha}, got {actual}")
    sections,old=prior_records(data,set(overlay),v4r,overlay)
    all_logs=[]; nums={i:[] for i in overlay}
    for _,_,row in sections["bug_investigation_logs"]:
        m=LOG_PREFIX.match(row)
        if m:
            bug=m.group(1).decode("ascii"); n=int(m.group(2)); all_logs.append((bug,n,row))
            if bug in nums:
                if n<0 or n>=MAX_LINE: raise ValueError(f"invalid line number for {bug}")
                nums[bug].append(n)
        else:
            for bug in overlay:
                if row.lstrip().startswith(bug.encode()+b","): raise ValueError(f"malformed target log row: {bug}")
    built={}; rows=[]; maxima=[]
    for bug in sorted(overlay):
        cat=categories[bug]; previous=old[bug]; payload,digest,f=new_fields(bug,cat,bug in pending,previous[1],overlay[bug][0],overlay[bug][1],digests)
        existing=previous[3]
        if existing:
            num,row,fields=existing[0][1],existing[0][2],existing[0][3]
            if fields.get("record_sha256")!=digest or row.strip().split(b",",2)[2].strip()!=payload:
                raise ValueError(f"same-campaign/ID payload conflict: {bug}")
            if sum(1 for b,n,_ in all_logs if b==bug and n==num)!=1: raise ValueError(f"existing V5 line number collision: {bug}")
        else:
            if len(nums[bug])!=len(set(nums[bug])): raise ValueError(f"preexisting target line number collision: {bug}")
            num=max(nums[bug],default=-1)+1
            if num>=MAX_LINE: raise ValueError(f"line number exhausted for {bug}")
            rows.append(f"    {bug}, {num}, ".encode()+payload+b"\n")
        built[bug]=(payload,digest,num,f)
        maxima.append(len(payload))
    insertion=b"".join(rows)
    _,at=tables(data)
    transformed=data[:at]+insertion+data[at:]
    return transformed,{"inserted":insertion,"built":built,"max_payload":max(maxima),"old":old,"no_op":not insertion}

def validate(candidate: bytes, baseline: bytes, meta: dict, categories: dict, pending: set, v4r: dict, overlay: dict, digests: dict):
    crc(candidate)
    sections,_=tables(candidate)
    found={}
    for _,_,row in sections["bug_investigation_logs"]:
        m=LOG_PREFIX.match(row)
        if not m: continue
        bug=m.group(1).decode("ascii")
        if bug in overlay:
            num=int(m.group(2)); payload=row[m.end():].strip(); fields=parse_payload(payload)
            if fields.get("audit")==CAMPAIGN:
                if bug in found: raise ValueError(f"duplicate V5 row {bug}")
                found[bug]=(num,payload,fields)
    if set(found)!=set(overlay): raise ValueError(f"V5 row set mismatch: {len(found)}")
    for bug,(num,payload,fields) in found.items():
        expected,digest,want=new_fields(bug,categories[bug],bug in pending,meta["old"][bug][1],overlay[bug][0],overlay[bug][1],digests)
        if payload!=expected or fields.get("record_sha256")!=digest or fields.get("scope")!="UNRUN" or fields.get("reproducibility")!="untested": raise ValueError(f"V5 payload mapping mismatch: {bug}")
        if num!=meta["built"][bug][2]: raise ValueError(f"V5 line allocation changed: {bug}")
    if sum(1 for _,_,f in found.values() if f["review"]=="accepted")!=6 or sum(1 for _,_,f in found.values() if f["review"]=="needs_more_evidence")!=25:
        raise ValueError("V5 revision review counts are not 6/25")
    # Reconstruct byte-exactly by deleting only this insertion block and restoring original CRC.
    back=candidate
    if meta["inserted"]:
        if back.count(meta["inserted"])!=1: raise ValueError("inserted block not unique")
        back=back.replace(meta["inserted"],b"",1)
    back=baseline.split(b"\n",1)[0]+b"\n"+back.split(b"\n",1)[1]
    if back!=baseline: raise ValueError("inverse reconstruction differs from exact baseline")
    if sha(back)!=sha(baseline): raise ValueError("inverse baseline digest mismatch")
    return {"rows":len(found),"accepted":6,"pending":25,"max_payload":meta["max_payload"],"inserted_sha256":sha(meta["inserted"])}

def acquire(path: Path):
    token=f"{os.getpid()}\n{time.time_ns()//1000}\n".encode("ascii")
    fd=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
    try:
        view=memoryview(token)
        while view:
            view=view[os.write(fd,view):]
        os.fsync(fd)
        st=os.fstat(fd)
        return fd,(st.st_dev,st.st_ino),token
    except Exception:
        st=os.fstat(fd)
        try:
            current=path.lstat()
            if not path.is_symlink() and (current.st_dev,current.st_ino)==(st.st_dev,st.st_ino):
                path.unlink()
        finally:
            os.close(fd)
        raise

def release(path: Path,fd,identity,token):
    try:
        if path.is_symlink(): return False
        st=path.stat()
        if (st.st_dev,st.st_ino)!=identity or path.read_bytes()!=token: return False
        path.unlink(); return True
    except FileNotFoundError: return False
    finally: os.close(fd)

def checked_lock(path: Path, identity, token):
    if DB.is_symlink() or Path(str(DB)+".wal").is_symlink() or path.is_symlink():
        raise ValueError("DB/WAL/lock symlink appeared while locked")
    st=path.stat()
    if (st.st_dev,st.st_ino)!=identity or path.read_bytes()!=token:
        raise ValueError("owned lock inode/token changed")
    wal=Path(str(DB)+".wal")
    if wal.exists() and wal.stat().st_size: raise ValueError("nonempty WAL appeared while locked")

def lock_fixtures():
    with tempfile.TemporaryDirectory(prefix="v5triage-lock-") as d:
        p=Path(d)/"db.lock"; foreign=b"foreign-owner\n"
        p.write_bytes(foreign)
        try: acquire(p); raise AssertionError("existing lock acquired")
        except FileExistsError: assert p.read_bytes()==foreign
        p.unlink(); fd,identity,token=acquire(p)
        try: raise RuntimeError("injected error")
        except RuntimeError: pass
        assert release(p,fd,identity,token) and not p.exists()
        fd,identity,token=acquire(p); p.unlink(); p.write_bytes(foreign)
        assert not release(p,fd,identity,token) and p.read_bytes()==foreign
        p.unlink()
        sync=os.fsync
        os.fsync=lambda _fd: (_ for _ in ()).throw(OSError("injected fsync failure"))
        try:
            try: acquire(p); raise AssertionError("injected fsync failure ignored")
            except OSError as e: assert "injected fsync failure" in str(e)
            assert not p.exists(), "owned lock leaked after write/fsync failure"
        finally:
            os.fsync=sync
    return "PASS"

def concurrent_replan_check(categories,pending,v4r,overlay,digests,baseline,bug):
    sections,_=tables(baseline)
    active=[]
    for t in ("bugs_active","bugs"):
        active += [r for _,_,r in sections.get(t,[]) if (m:=ROW_ID.match(r)) and m.group(1).decode()==bug]
    logs=[r for _,_,r in sections["bug_investigation_logs"] if (m:=LOG_PREFIX.match(r)) and m.group(1).decode()==bug and b"audit="+V4_CAMPAIGN.encode() in r]
    if len(active)!=1 or len(logs)!=1: raise ValueError("concurrent fixture target is not unique")
    other=b"    scratch_unrelated, P2, open, source_revision_a\n"
    fixture=b"#sdn-crc32:0\n"+b"bugs_active |id, priority, status, title|\n"+active[0]+other+b"\nbugs |id, priority, status, title|\n"+active[0]+b"\n\nbug_investigation_logs |bug_id, line_num, content|\n"+logs[0]
    fixture,_=reseal(fixture)
    sealed,meta=plan(fixture,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests)
    sealed,_=reseal(sealed)
    changed=sealed.replace(b"source_revision_a",b"source_revision_b",1)
    if changed==sealed: raise AssertionError("fixture concurrency edit was a no-op")
    result,_=plan(changed,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests)
    if b"source_revision_b" not in result: raise AssertionError("replan dropped unrelated concurrent mutation")
    return "PASS"

def scratch(categories,pending,v4r,overlay,digests,baseline):
    # Reuse a byte slice of the real DB containing one target's row and exact V4 comment.
    bug=sorted(overlay)[0]
    sections,_=tables(baseline)
    active=[]
    for t in ("bugs_active","bugs"):
        active += [r for _,_,r in sections.get(t,[]) if (m:=ROW_ID.match(r)) and m.group(1).decode()==bug]
    log=[r for _,_,r in sections["bug_investigation_logs"] if (m:=LOG_PREFIX.match(r)) and m.group(1).decode()==bug and b"audit="+V4_CAMPAIGN.encode() in r]
    if len(active)!=1 or len(log)!=1: raise ValueError("scratch fixture target is not unique")
    unrelated=b"    scratch_unrelated, P2, open, source_revision_a\n"
    mini=b"#sdn-crc32:0\n"+b"bugs_active |id, priority, status, title|\n"+active[0]+unrelated+b"\nbugs |id, priority, status, title|\n"+active[0]+b"\n\nbug_investigation_logs |bug_id, line_num, content|\n"+log[0]
    mini,_=reseal(mini)
    one,meta=plan(mini,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests)
    sealed,_=reseal(one)
    again,m2=plan(sealed,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests)
    assert again==sealed and m2["no_op"]
    try: plan(mini,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests,"0"*64); raise AssertionError("stale CAS accepted")
    except ValueError as e: assert "stale database CAS" in str(e)
    bad=sealed.replace(meta["built"][bug][0],b"audit="+CAMPAIGN.encode()+b" revision=99")
    try: plan(bad,{bug:categories[bug]},({bug} if bug in pending else set()),v4r,{bug:overlay[bug]},digests); raise AssertionError("same campaign conflict accepted")
    except ValueError as e: assert "conflict" in str(e)
    assert concurrent_replan_check(categories,pending,v4r,overlay,digests,baseline,bug)=="PASS"
    assert reconstruct_scratch(sealed,meta,mini)
    lock_result=lock_fixtures()
    return {"idempotence":"PASS","stale_cas":"PASS","same_campaign_conflict":"PASS","concurrent_replan":"PASS","inverse":"PASS","lock":lock_result}

def reconstruct_scratch(candidate,meta,baseline):
    back=candidate.replace(meta["inserted"],b"",1)
    back=baseline.split(b"\n",1)[0]+b"\n"+back.split(b"\n",1)[1]
    return back==baseline

def main():
    ap=argparse.ArgumentParser(); g=ap.add_mutually_exclusive_group(required=True); g.add_argument("--prepare",action="store_true"); g.add_argument("--install",action="store_true"); g.add_argument("--validate",action="store_true"); args=ap.parse_args()
    categories,pending,v4r,overlay,digests=check_inputs()
    baseline=DB.read_bytes()
    candidate_path=Path(str(DB)+".v5-candidate")
    if args.prepare:
        if DB.is_symlink() or Path(str(DB)+".lock").exists() or (Path(str(DB)+".wal").exists() and Path(str(DB)+".wal").stat().st_size): raise ValueError("DB symlink/lock/WAL precondition")
        if sha(baseline)!=BASE_DB_SHA: raise ValueError(f"fixed source DB mismatch {sha(baseline)}")
        crc_before=crc(baseline)
        transformed,meta=plan(baseline,categories,pending,v4r,overlay,digests,BASE_DB_SHA)
        candidate,new_crc=reseal(transformed)
        checked=validate(candidate,baseline,meta,categories,pending,v4r,overlay,digests)
        fixtures=scratch(categories,pending,v4r,overlay,digests,baseline)
        if candidate_path.is_symlink() or candidate_path.exists(): raise ValueError("candidate path already exists")
        fd=os.open(candidate_path,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
        with os.fdopen(fd,"wb") as f: f.write(candidate); f.flush(); os.fsync(f.fileno())
        rows="".join(f"    {bug}, {v[2]}, {v[1]}\n" for bug,v in sorted(meta["built"].items()))
        receipt=[("state","candidate_prepared","installation awaits exact Astra GO"),("source_base",BASE,"release/1.0.0 immutable application base"),("evidence_commit",EVIDENCE_COMMIT,"merged V5 evidence checkpoint"),("baseline_database_sha256",sha(baseline),"exact byte snapshot"),("candidate_database_sha256",sha(candidate),"append-only V5 note candidate"),("baseline_crc32",str(crc_before),"CRC-32 ISO-HDLC"),("candidate_crc32",str(new_crc),"CRC-32 ISO-HDLC"),("v4_residual_sha256",digests["v4_residual"],"exact 31-ID superseded set"),("v5_categories_sha256",digests["v5_categories"],"1577 accepted category rows"),("v5_residual_sha256",digests["v5_residual"],"25 remaining pending rows"),("overlay_sha256",digests["overlay"],"31 exact CSV records; LF included in per-row SHA"),("overlay_row_hash_framing","physical CSV bytes including terminal LF","overlay_row_sha256 binds exact source bytes"),("manifest_sha256",digests["manifest"],"committed evidence manifest"),("detail_evidence_sha256",digests["detail"],"committed rationale detail file"),("revision_accounting","31","accepted=6 needs_more_evidence=25; all reproducibility=untested scope=UNRUN"),("supersession","31","each supersedes exact V4 semantic record_sha256"),("reproduction","1 HOST_PROTOCOL","existing reproduction is outside this set; other 1601 remain untested"),("inserted_rows",str(checked["rows"]),"max+1 unique line numbers"),("max_payload_bytes",str(checked["max_payload"]),f"explicit limit {MAX_PAYLOAD}; no truncation"),("inserted_block_sha256",checked["inserted_sha256"],"exact new log-row block"),("inverse_reconstruction","PASS","deleting insertion and restoring CRC recreates exact baseline SHA"),("scratch_idempotence",fixtures["idempotence"],"same payload is verified zero-byte no-op"),("scratch_stale_cas",fixtures["stale_cas"],"stale baseline refused"),("scratch_conflict",fixtures["same_campaign_conflict"],"different same-campaign payload refused"),("scratch_concurrent_replan",fixtures["concurrent_replan"],"unrelated row change retained"),("scratch_lock",fixtures["lock"],"exclusive native PID/usec owner lock and inode/token cleanup"),("database_status_dates_valid","UNCHANGED","no status/date/valid cells permitted"),("native_owner_roundtrip","UNRUN","no compiler seed native owner or full CLI qualification"),("retry_scope","fixed_base_one_off","post-commit rerun is refused by fixed HEAD guard; precommit same-campaign no-op fixture tested")]
        RECEIPT.write_text("triage_v5_revision2_application |item,value,detail|\n"+"".join(f"    {a}, {b}, {c}\n" for a,b,c in receipt),encoding="ascii")
        (TRIAGE/"v5_revision2_note_hashes.sdn").write_text("triage_v5_revision2_note_hashes |bug_id,line_num,record_sha256|\n"+rows,encoding="ascii")
        print(f"prepared={candidate_path} baseline={sha(baseline)} candidate={sha(candidate)} crc32={crc_before}->{new_crc} rows={checked['rows']} max_payload={checked['max_payload']}")
        print("scratch="+",".join(f"{k}:{v}" for k,v in fixtures.items()))
        return 0
    if args.validate:
        candidate=candidate_path.read_bytes(); print(f"candidate_sha256={sha(candidate)} crc32={crc(candidate)}"); return 0
    lock_path=Path(str(DB)+".lock")
    if DB.is_symlink() or lock_path.is_symlink() or Path(str(DB)+".wal").is_symlink(): raise ValueError("DB/WAL/lock symlink refused")
    if lock_path.exists() or (Path(str(DB)+".wal").exists() and Path(str(DB)+".wal").stat().st_size): raise ValueError("live lock/nonempty WAL refused")
    fd,identity,token=acquire(lock_path)
    try:
        checked_lock(lock_path,identity,token)
        baseline=DB.read_bytes()
        if sha(baseline)!=BASE_DB_SHA:
            # Identical complete state is a verified no-op; all partial or conflicting states fail.
            transformed,meta=plan(baseline,categories,pending,v4r,overlay,digests)
            if not meta["no_op"] or transformed!=baseline: raise ValueError("fixed source CAS changed; partial/changed DB requires semantic replan")
            validate(baseline,baseline,meta,categories,pending,v4r,overlay,digests)
            print(f"already_applied=verified_no_op sha256={sha(baseline)} crc32={crc(baseline)} rows=31")
            return 0
        if candidate_path.is_symlink(): raise ValueError("candidate symlink refused")
        candidate=candidate_path.read_bytes()
        transformed,meta=plan(baseline,categories,pending,v4r,overlay,digests,BASE_DB_SHA)
        expected,new_crc=reseal(transformed)
        validate(candidate,baseline,{**meta,"inserted":meta["inserted"]},categories,pending,v4r,overlay,digests)
        if candidate!=expected or crc(candidate)!=new_crc: raise ValueError("candidate differs from reviewed deterministic plan")
        resealer=ROOT/"scripts/check/reseal-sdn-crc32.shs"
        result=subprocess.run(["sh",str(resealer),str(candidate_path)],cwd=ROOT,capture_output=True,text=True,check=False)
        if result.returncode or "already " not in result.stdout: raise ValueError(f"existing resealer rejected candidate: {result.stdout}{result.stderr}")
        checked_lock(lock_path,identity,token)
        if DB.read_bytes()!=baseline: raise ValueError("final byte CAS failed while holding DB lock")
        os.replace(candidate_path,DB)
        if DB.read_bytes()!=candidate: raise ValueError("atomic replacement differs from validated candidate")
        print(f"installed_sha256={sha(candidate)} crc32={new_crc} inserted_rows=31")
    finally:
        if not release(lock_path,fd,identity,token): raise ValueError("owned lock cleanup failed; foreign lock preserved")
    return 0

if __name__=="__main__":
    try: sys.exit(main())
    except Exception as e: print(f"migration refused: {type(e).__name__}: {e}",file=sys.stderr); sys.exit(2)
