#!/usr/bin/env perl
use strict; use warnings;
use Cwd qw(realpath); use Digest::SHA qw(sha256_hex); use Errno qw(ENOENT);
use Fcntl qw(O_RDONLY O_WRONLY O_CREAT O_EXCL O_DIRECTORY O_NOFOLLOW);
use File::Basename qw(dirname basename); use File::Find;

@ARGV == 8 or die "usage: $0 MODE STAGING FINAL MARKER COMPAT INPUTS HASH STAMP_HASH\n";
my ($mode,$staging,$final,$marker,$compat,$inputs,$hash,$stamp_hash)=@ARGV;
$mode eq 'new'||$mode eq 'existing' or die "invalid publication mode\n";
$inputs=~/\A[0-9a-f]{64}\z/&&$hash=~/\A[0-9a-f]{64}\z/&&$stamp_hash=~/\A[0-9a-f]{64}\z/ or die "invalid publication digest\n";
dirname($staging) eq dirname($final) or die "generation publication parents differ\n";
my $generation_path=dirname($final); my $control_path=dirname($marker);
dirname($compat) eq $control_path&&dirname($generation_path) eq $control_path or die "authority control paths differ\n";
for my $path($generation_path,$control_path){my $canonical=realpath($path);defined($canonical)&&$canonical eq $path or die "authority parent is not canonical\n";}
my($stage_leaf,$final_leaf,$generation_leaf,$marker_leaf,$compat_leaf)=(basename($staging),basename($final),basename($generation_path),basename($marker),basename($compat));
for my $leaf($stage_leaf,$final_leaf,$generation_leaf,$marker_leaf,$compat_leaf){$leaf=~/\A[A-Za-z0-9._-]+\z/&&$leaf ne q{.}&&$leaf ne q{..} or die "unsafe authority leaf\n";}
my $open_dir=O_RDONLY|O_DIRECTORY|O_NOFOLLOW;
sysopen(my $control,$control_path,$open_dir) or die "open control parent: $!\n"; my @control_id=stat($control);
chdir($control) or die "bind control parent: $!\n";
sysopen(my $generation,$generation_leaf,$open_dir) or die "open generation parent: $!\n"; my @generation_id=stat($generation);
chdir($generation) or die "bind generation parent: $!\n";
my @bound_generation=stat(q{.}); @bound_generation&&$bound_generation[0]==$generation_id[0]&&$bound_generation[1]==$generation_id[1] or die "generation parent changed\n";
my @prepared=lstat($mode eq 'new'?$stage_leaf:$final_leaf); @prepared&&-d _&&!-l _ or die "prepared generation is not physical\n";
my $final_present=$mode eq 'existing';
if($mode eq 'new'){!lstat($final_leaf)&&$!==ENOENT or die "generation final exists\n";rename($stage_leaf,$final_leaf) or die "atomic generation rename: $!\n";$final_present=1;}
my @final_id=lstat($final_leaf); @final_id&&$final_id[0]==$prepared[0]&&$final_id[1]==$prepared[1]&&-d _&&!-l _ or die "published generation identity changed\n";
my $failure;
if(($ENV{SIMPLE_BOOTSTRAP_TEST_AUTHORITY_PUBLISH_FAIL_FREEZE}//q{}) eq 1){$failure="injected generation freeze failure\n";}elsif(!chmod(0500,$final_leaf)){$failure="freeze published generation: $!\n";}
if(($ENV{SIMPLE_BOOTSTRAP_TEST_AUTHORITY_PUBLISH_RACE_AFTER_FREEZE}//q{}) eq 1){chdir($control) or die "rebind control for race: $!\n";my $swapped="$control_path.swapped.$$";rename($control_path,$swapped) or die "inject control swap: $!\n";mkdir($control_path,0700) or die "inject replacement control: $!\n";chdir($generation) or die "restore generation descriptor: $!\n";}
my $visible_control=realpath($control_path);my @visible_control_id=defined($visible_control)?stat($control_path):();
my $visible_generation=realpath($generation_path);my @visible_generation_id=defined($visible_generation)?stat($generation_path):();
if(!defined($visible_control)||$visible_control ne $control_path||!@visible_control_id||$visible_control_id[0]!=$control_id[0]||$visible_control_id[1]!=$control_id[1]||!defined($visible_generation)||$visible_generation ne $generation_path||!@visible_generation_id||$visible_generation_id[0]!=$generation_id[0]||$visible_generation_id[1]!=$generation_id[1]){$failure||="authority parent changed after generation freeze\n";}
my $quarantine=sub{return unless $final_present&&$mode eq 'new';chdir($generation) or die "bind generation for quarantine: $!\n";for my $attempt(0..1023){my $candidate=".rejected.$final_leaf.$$.$attempt";next if lstat($candidate);if(rename($final_leaf,$candidate)){chmod(0500,$candidate);$final_present=0;return;}}die "could not quarantine failed generation\n";};
if(defined($failure)){$quarantine->();die $failure;}

chdir($control) or die "bind control for admission: $!\n";
my $transaction_leaf="$marker_leaf.transaction";
my $transaction_tmp="$transaction_leaf.tmp.$$";
my $marker_tmp="$marker_leaf.tmp.$$";
my $compat_tmp=".compat.$compat_leaf.$$";
my $compat_backup=".compat-backup.$compat_leaf.$$";
my $transaction_body="schema=simple-bootstrap-authority-transaction-v1\ngeneration=$final_leaf\ninputs_fingerprint=$inputs\ngeneration_sha256=$hash\nstamp_sha256=$stamp_hash\n";
my $marker_body="schema=simple-bootstrap-authority-current-v1\ngeneration=$final_leaf\ninputs_fingerprint=$inputs\ngeneration_sha256=$hash\nstamp_sha256=$stamp_hash\n";
my $write_atomic=sub{my($tmp,$dest,$body)=@_;sysopen(my $fh,$tmp,O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW,0600) or die "create control temporary: $!\n";print {$fh}$body or die "write control temporary: $!\n";close($fh) or die "close control temporary: $!\n";rename($tmp,$dest) or die "commit control file: $!\n";};
my($compat_saved,$compat_installed,$error)=(0,0);
eval{$write_atomic->($transaction_tmp,$transaction_leaf,$transaction_body);if(lstat($compat_leaf)){rename($compat_leaf,$compat_backup) or die "save compatibility: $!\n";$compat_saved=1;}symlink("$generation_leaf/$final_leaf",$compat_tmp) or die "create compatibility: $!\n";rename($compat_tmp,$compat_leaf) or die "commit compatibility: $!\n";$compat_installed=1;if(($ENV{BOOTSTRAP_STAGE3_TEST_STOP_AFTER_COMPATIBILITY}//q{}) eq 1){die "__STOP_AFTER_COMPATIBILITY__\n";}$write_atomic->($marker_tmp,$marker_leaf,$marker_body);my $control_after=realpath($control_path);my @control_after_id=defined($control_after)?stat($control_path):();defined($control_after)&&$control_after eq $control_path&&@control_after_id&&$control_after_id[0]==$control_id[0]&&$control_after_id[1]==$control_id[1] or die "authority control parent changed during marker admission\n";unlink($transaction_leaf) or die "retire transaction: $!\n";
if($compat_saved){if(-d $compat_backup&&!-l $compat_backup){my @records;find({no_chdir=>1,wanted=>sub{return if $File::Find::name eq $compat_backup;-l $File::Find::name and die "legacy symlink\n";return unless -f $File::Find::name;my $sha=Digest::SHA->new(256);$sha->addfile($File::Find::name,'b');my $relative=substr($File::Find::name,length($compat_backup)+1);push @records,join(':','file-hex',unpack('H*',$relative),(-x $File::Find::name?1:0),$sha->hexdigest);}},$compat_backup);@records or die "empty legacy authority\n";my $legacy="$generation_leaf/legacy-".sha256_hex(join("\n",sort @records)."\n");rename($compat_backup,$legacy) or die "archive legacy compatibility: $!\n";}else{unlink($compat_backup) or die "retire old compatibility: $!\n";}}1;}or$error=$@||"authority admission failed\n";
if(defined($error)&&$error eq "__STOP_AFTER_COMPATIBILITY__\n"){exit 99;}
if(defined($error)){unlink($marker_leaf);unlink($marker_tmp);unlink($transaction_leaf);unlink($transaction_tmp);unlink($compat_tmp);unlink($compat_leaf) if $compat_installed;rename($compat_backup,$compat_leaf) if $compat_saved&&lstat($compat_backup);$quarantine->();die $error;}
exit 0;
