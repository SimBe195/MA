#!/bin/sh

# htmltostd.sh
# Converts lattice file from html format to standard library format
# Takes latt.html and creates latt.std

if [ "$#" -ne 1 ]
then
echo "Incorrect number of arguments.
htmltostd.sh converts file for a lattice from html format
to standard library format.
Takes latt.html and creates latt.std
Usage: htmltostd.sh latt.html"
exit 1
fi 

latt1="$1"
latt2=`echo $latt1 | sed 's/html/std/'`
echo "Using $latt1 to create $latt2"

# perform various checks
if [ ! -f $latt1 ]
then
echo "$latt1 does not exist"
exit 1
fi

if [ -f $latt2 ]
then
echo "$latt2 exists: OK to overwrite? [y/n]"
read answer
	if [ "$answer" != y ]
	then
	exit 1
	fi
fi

# Now do the editing:
#    delete banners etc at start and end, 
#    delete all html commands,
#    change &lt; to "less than",
#    and &gt; to "greater than".


cp $latt1 $latt2

ex - $latt2 <<!
1,/NAME=/-1d
/LAST_LINE/1,\$d
g/NAME=/s/<\/b.*\$//
g/NAME=/s/^.*<STRONG>/\%/
g/^</d
g//s///g
g/\&lt;/s//</g
g/\&gt;/s//>/g
w
q
!

exit
