use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductRoot qw(allocate_product_root resolve_product_root mirror_product_receipt);
use BootstrapProductOverlay;
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use File::Basename qw(dirname);
use Test::More;
my $windows = $^O eq 'msys' || $^O eq 'cygwin';
my $junction_only = @ARGV == 1 && $ARGV[0] eq '--junction-only';
my $base = $windows ? '/c/.simple-product-tests' : '/tmp';
make_path($base);
my $f = tempdir('boundaries-XXXXXXXX', DIR => $base, CLEANUP => 0);
note("retained boundary fixture: $f");
my $s = "$f/source"; make_path($s);
sub put { my($p,$b)=@_; make_path(dirname($p)); open my $h,'>:raw',$p or die $!; print {$h} $b; close $h or die $!; }
sub get { open my $h,'<:raw',$_[0] or die $!; local $/; return <$h>; }
sub git { system('git','-C',$s,'-c','core.hooksPath=NUL','-c','core.autocrlf=false','-c','user.name=Fixture','-c','user.email=fixture@example.invalid',@_)==0 or die 'Git fixture failed'; }
sub reject { my($fn,$pattern,$label)=@_; eval{$fn->();1} and die "unexpected success: $label"; like($@,$pattern,$label); }
sub alias {
    my($p,$target)=@_; put("$s/$p",$target);
    my $oid=BootstrapProductOverlay::git_bytes($s,'hash-object','-w',$p); chomp $oid;
    git('update-index','--add','--cacheinfo',"120000,$oid,$p");
}
git('init','-q');
put("$s/src/app/main.spl",'source'); git('add','.'); git('commit','-qm','base');
if($windows) {
    my $a="$f/anchor"; make_path($a);
    put("$a/source-snapshot.txt",'snapshot'); put("$a/source-specs.tsv",'inventory');
    put("$f/compiler",'compiler'); put("$f/receipt",'unqualified test evidence');
    my $r=allocate_product_root($a,$s,"$a/source-snapshot.txt","$a/source-specs.tsv","$f/compiler","$f/receipt",'','');
    unless ($junction_only) {
    reject(sub{resolve_product_root($a,$s,"$f/compiler","$f/receipt","$f/compiler","$f/receipt")},qr/new producer/,'missing producer cannot be silently added on resume');
    reject(sub{allocate_product_root("$f",'/c/.simple-product-jobs',"$f/source-snapshot.txt","$f/source-specs.tsv",'','','','')},qr/overlaps source/,'physical allocated root cannot overlap source');
    my $receipt="binary_path=$r/llvm/compiler/product\nmanifest_path=$r/llvm/compiler/manifest.tsv\nexecuted=7\nfailed=2\nstatus=FAIL\n";
    put("$r/llvm/compiler/result.env",$receipt);
    my $dest=mirror_product_receipt($a,$s,'llvm','compiler');
    is(get($dest),$receipt,'mirror preserves exact physical paths, manifest and failure counts');
    reject(sub{mirror_product_receipt($a,$s,'llvm','compiler')},qr/already exists/,'mirror never overwrites prior evidence');
    reject(sub{mirror_product_receipt($a,$s,'llvm','../foreign')},qr/selector/,'mirror rejects selector traversal');
    }
    my $junction="$r/link";
    sub win { my $p=shift; $p =~ s{^/([a-zA-Z])/}{$1:/}; $p =~ tr{/}{\\}; return $p; }
    local $ENV{MSYS2_ARG_CONV_EXCL} = '*';
    local $ENV{MSYS_NO_PATHCONV} = '1';
    my $rc=system('cmd.exe','/d','/c','mklink','/J',win($junction),win($s));
    if($rc==0) {
        reject(sub{BootstrapProductRoot::safe($junction,1)},qr/link/,'real Windows directory junction rejected');
    } else { fail('Windows junction fixture creation must succeed for this host test'); }
}
unless ($junction_only) {
alias('src/app/a','b'); alias('src/app/b','a'); git('commit','-qm','cycle fixture');
reject(sub{BootstrapProductOverlay::plan($s)},qr/cyclic/,'declared alias cycle rejected');
alias('src/app/a','missing'); git('commit','-qm','missing fixture');
reject(sub{BootstrapProductOverlay::plan($s)},qr/missing declared/,'missing target rejected');
alias('src/app/a','../../../outside'); git('commit','-qm','escape fixture');
reject(sub{BootstrapProductOverlay::plan($s)},qr/escapes source/,'declared target escape rejected');
}
done_testing();
