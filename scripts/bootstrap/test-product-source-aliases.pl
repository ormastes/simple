use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductOverlay qw(verify_product_source);
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use File::Basename qw(dirname);
use Test::More;
my $base = $^O =~ /msys|cygwin/ ? '/c/.simple-product-tests' : '/tmp';
make_path($base);
my $s = tempdir('source-alias-XXXXXXXX', DIR => $base, CLEANUP => 0);
note("retained source alias fixture: $s");
sub put { my($p,$b)=@_; make_path(dirname($p)); open my $h,'>:raw',$p or die $!; print {$h} $b; close $h or die $!; }
sub git { system('git','-C',$s,'-c','core.hooksPath=NUL','-c','core.autocrlf=false','-c','user.name=Fixture','-c','user.email=fixture@example.invalid',@_)==0 or die 'Git fixture failed'; }
sub reject { my($fn,$pattern,$label)=@_; eval{$fn->();1} and die "unexpected success: $label"; like($@,$pattern,$label); }
git('init','-q');
put("$s/src/app/actual/main.spl",'canonical target');
put("$s/src/app/alias",'actual');
put("$s/src/app/file_alias.spl",'actual/main.spl');
git('add','.');
for my $path ('src/app/alias','src/app/file_alias.spl') {
    my $oid=BootstrapProductOverlay::git_bytes($s,'hash-object',$path); chomp $oid;
    git('update-index','--cacheinfo',"120000,$oid,$path");
}
git('commit','-qm','declared alias fixture');
unlink "$s/src/app/alias" or die $!;
put("$s/src/app/alias/main.spl",'canonical target');
put("$s/src/app/file_alias.spl",'canonical target');
ok(verify_product_source($s),'real directory and file expansions pass exact source clean gate');
put("$s/src/app/alias/main.spl",'corruption');
reject(sub{verify_product_source($s)},qr/alias bytes differ/,'changed alias bytes rejected');
put("$s/src/app/alias/main.spl",'canonical target');
put("$s/src/app/alias/extra.spl",'extra member');
reject(sub{verify_product_source($s)},qr/non-alias changes/,'undeclared alias descendant rejected');
unlink "$s/src/app/alias/extra.spl" or die $!;
put("$s/src/app/actual/main.spl",'changed canonical target');
put("$s/src/app/alias/main.spl",'changed canonical target');
put("$s/src/app/file_alias.spl",'changed canonical target');
reject(sub{verify_product_source($s)},qr/non-alias changes/,'matching aliases do not exempt changed declaring source');
put("$s/src/app/actual/main.spl",'canonical target');
put("$s/src/app/alias/main.spl",'canonical target');
put("$s/src/app/file_alias.spl",'canonical target');
git('add','src/app/file_alias.spl');
reject(sub{verify_product_source($s)},qr/non-alias changes/,'staged alias mode changes rejected');
done_testing();
