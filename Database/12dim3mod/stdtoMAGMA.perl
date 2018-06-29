#!/usr/bin/perl
# stdtoMAGMA.perl   Perl script to make MAGMA readable
# version of gram matrix from standard library file
# Last modified Jun 06 1997
# Thanks to Bernd Souvignier and Allan Steel for some improvements

if ( $#ARGV != 0 )
 { die "Useage: stdtoMAGMA.perl file.std >out then run magma
then type: load \"out\";      " }


# check file name ends in .std
if ( ! $ARGV[0] =~ /\.std$/) { die "filename doesn't end with .std!     "}

# check if file exists
if ( ! -f $ARGV[0] )  { die "$ARGV[0] does not exist!    " }

# open lattice file ($1)
open(LATTICE,$ARGV[0]);

# states:  0 = neutral, 1 means have just read "^%GRAM", 
# 2 means reading Gram matrix
$state = "0";

# set up empty list to hold Gram matrix
@gramlist = ();

# read all input lines
while (<LATTICE>) {
	chop;  # delete newline at end
	$_ =~ s/^  *//;   # delete leading blanks
	$line = $_;
	@line = split;   # break up into a list

	if ( $#line < 0 ) {next }   # skip if empty line

	if ($line[0] =~ /^%/) { $state = "0" }  #reset state to 0 if find %

	if ($line[0] =~ /^%GRAM$/) {    # look for line beginning %GRAM
		$state = "1";           # sets state to 1, getting ready
					# for reading dimensions on next line
		next;              }

	if ($state =~ "1") { $d1 = $line[0];    # state = 1,
						# so read dimensions of array
                             $d2 = $line[1];
			     $state = "2";      # and set state to 2
			     next;
                           }  

	if ($state =~ "2" && $line[0] !~ /^%/) {    # reading Gram matrix
		$t1 = $#line;    # get no of entries on the current line
# add then to gram matrix
		push( @gramlist, @line)        }

	if ($line[0] =~ /^%MINIMAL_NORM$/) { 
		$state = "3";
	}

	if ($state =~ "3") {
		$min = $line;
	}
    
                  }

# print in MAGMA format, calling the lattice "L"

# print LHS

for ($i = 0; $i < @gramlist; $i++)
{
    $gramlist[$i] = $gramlist[$i] + 0;
}

print("L := LatticeWithGram($d1, [\n");
for ($i = 0; $i < $d1; $i++)
{
    @g = ();
    if ($d2)
    {
	@g = @gramlist[$i * $d2 .. $i * $d2 + $i];
    }
    else
    {
	for ($j = 0; $j <= $i; $j++)
	{
	    push(@g, shift @gramlist);
	}
    }
    $j = join(',', @g);
    print "    $j";
    if ($i < $d1 - 1)
    {
	print ",";
    }
    print "\n";
}
print "]);\n";

if (defined $min)
{
    $min = $min + 0;
    print "L`Minimum := $min;\n";
}

