#!/usr/bin/perl

my $branchfile = "branch.log";
`touch $branchfile`;

my $defaultbranch = "main";
my %patches = ( "unit" => "unit.diff", "hide" => "hide.diff" );
$patches{$defaultbranch} = "";
my @branches = keys %patches;

print "Availables branches = ", join(" ",@branches), "\n";

my $source = `tail -n1 "$branchfile"`;
chomp $source;
$source = $defaultbranch unless $source;

print "Current branch = $source (according to log file $branchfile)\n";

my $target = shift;

die "Target branch \"$target\" is undefined, exiting" unless exists $patches{$target};
die "Target branch \"$target\" is the same as current branch \"$source\", exiting" if $source eq $target;

# switch from source branch to default branch
if ($source ne $defaultbranch) {
  $patchfile = $patches{$source};
  print "Switching to branch $defaultbranch using patch file $patchfile (reversed)\n";
  `patch --reverse < "$patchfile"`;
  `echo $defaultbranch >> "$branchfile"`;
  }
  
#switch from default branch to target branch
if ($defaultbranch ne $target) {
  $patchfile = $patches{$target};
  print "Switching to branch $target using patch file $patchfile\n";
  `patch < "$patchfile"`;
  `echo $target >> "$branchfile"`;
  }

