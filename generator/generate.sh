#!/bin/sh
# Author: Martin Vassor
# Description: Generate a payload to test hashmap implementations
# Creation date: 07-10-2016
# Last modified: Fri Oct  7 17:31:03 2016
# Known bugs: 

print_help() {
	echo "Usage: $0 LENGTH [OPTION]"
}

terminate() {
	./Bash-collections/map.sh "$ARGS" remove
}

if [ $# -lt 1 ]; then
	print_help;
	exit -1;
fi

ARGS=$(./Bash-collections/map.sh new)

./Bash-collections/map.sh "$ARGS" put length "$1"
shift

for i in `seq $#`; do
	ARGNAME=$(echo "$1" | cut -c 3- | cut -d "=" -f1)
	ARGVAL=$(echo "$1" | cut -c 3- | cut -d "=" -f2)
	./Bash-collections/map.sh "$ARGS" put "$ARGNAME" "$ARGVAL"
	shift
done;

terminate

: <<=cut

=pod

=head1 NAME

generate.sh - A generator of payload to test hashmap implementations

=head1 SYNOPSIS

C<./generate LENGTH [OPTION]>

=head1 DESCRIPTION

=over 4

=item C<--capacity=capacity> Sets the capacity of the table. Used to compute the average load. The test will insert integer from 0 up to I<capacity>

=item C<--load=load> The target load. Does not guarantee to maintain this load all the time, to tries to achieve it.

=item C<--read=read> Proportion of read request versus write requests.

=back

=head1 AUTHOR

Martin Vassor, for DSLab, EPFL

=cut
