from pathlib import Path
import re,subprocess
root=Path(__file__).resolve().parents[2];out=root/'build/target-profile/cache';(out/'src').mkdir(parents=True,exist_ok=False)
def read(path):return(root/path).read_text()
def block(text,kind,name):
 lines=text.splitlines(True);start=next(i for i,s in enumerate(lines) if re.match(r'(?:pub )?'+kind+' '+name+r'\b',s));end=start+1
 while end<len(lines) and (not lines[end].strip() or lines[end].startswith(' ')):end+=1
 return ''.join(lines[start:end])
c=read('src/compiler/80.driver/cache/compile_options_hash.spl');sha=read('src/lib/common/crypto/sha256.spl');parts=[(root/'build/target-profile/green1/production.spl').read_text(),block(c,'struct','CompileOptionsHash')]
parts += [s+'\n' for s in c.splitlines() if s.startswith('val BACKEND_')]
for name in ['_coh_component','_coh_text_lt','_coh_sorted_text','_coh_sha256_prefix_i64','compile_options_hash_compute','backend_text_to_kind']:parts.append(block(c,'fn',name))
for name in ['_sha256_k','sha256_bytes']:parts.append(block(sha,'fn',name))
parts += [block(read('src/lib/common/crypto/word_ops.spl'),'fn','rotr32'),block(read('src/lib/common/crypto/types.spl'),'fn','crypto_text_to_bytes'),'extern fn rt_text_to_bytes(s: text) -> [u8]\nfn text_to_bytes(s: text) -> [i64]:\n    crypto_text_to_bytes(s)\n']
old=subprocess.check_output(['git','show','a132155869c:src/compiler/80.driver/cache/compile_options_hash.spl'],cwd=root,text=True)
parts.append(block(old,'fn','compile_options_hash_compute').replace('fn compile_options_hash_compute(', 'fn legacy_compile_options_hash_compute(',1))
parts.append('''fn main() -> i64:
    val dev0 = compile_options_hash_compute("llvm", 0, false, true, false, "dev", [])
    val dev3 = compile_options_hash_compute("llvm", 3, false, true, false, "dev", [])
    val prod0 = compile_options_hash_compute("llvm", 0, true, true, false, "prod", [])
    val legacy0 = legacy_compile_options_hash_compute("llvm", 0, false, true, false, "dev", [])
    if dev0.hash == dev3.hash or dev0.hash == prod0.hash or dev0.hash == legacy0.hash:
        print "FAIL profile optimization or legacy cache identity collision"
        return 1
    val first = NormalizedTargetProfileV1(TargetBuildProfileV1.Development, TargetDebugRequestV1.Default, TargetTraceResolutionV1.Unavailable("abc\\ntarget_trace_resolution=available"))
    val second = NormalizedTargetProfileV1(TargetBuildProfileV1.Development, TargetDebugRequestV1.Default, TargetTraceResolutionV1.Unavailable("abc"))
    val one = compile_options_hash_compute("llvm", 0, false, true, false, "dev", [], target_profile_identity: target_profile_identity_text_v1(first))
    val two = compile_options_hash_compute("llvm", 0, false, true, false, "dev", [], target_profile_identity: target_profile_identity_text_v1(second))
    if one.hash == two.hash or target_profile_identity_text_v1(first) == target_profile_identity_text_v1(second):
        print "FAIL framed unavailability identity collision"
        return 2
    print "PASS actual SHA256 cache profile optimization legacy invalidation and framed reason identity"
    0
''')
(out/'src/main.spl').write_text('\n'.join(parts));(out/'provenance.sdn').write_text('projection: "actual CompileOptions and compile_options_hash_compute plus actual SHA256 byte implementation"\nlegacy_revision: "a132155869c"\n')
print(out)
