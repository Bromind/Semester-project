#!/bin/sh
# Author: Martin Vassor
# Description: Compare the hashmap implementations with different load values
# Creation date: 14-10-2016
# Last modified: Fri Oct 14 15:36:40 2016
# Known bugs: 

print_help() {
	echo "Usage: $0 LENGTH READ LOAD1 [...]"
}

if [ $# -lt 3 ]; then
	print_help;
	exit -1;
fi;

LENGTH="$1"
READ="$2"
shift
shift

for i in `seq $#`; do
	echo "Generate test file of length $LENGTH, read ratio $READ, and load $1";
	./generate.sh "$LENGTH" --capacity=16384 --load="$1" --read="$READ" > test_files/l-"$LENGTH"_c-16384_l-"$1"_r-"$READ".mapctrl
	shift
done;

: <<=cut

=pod

=head1 NAME

test_load.sh - Generates a batch of test files with different load values

=head1 SYNOPSIS

C<test_load.sh LENGTH READ LOAD1 [...]"

=head1 AUTHOR

Martin Vassor, for DSLab, EPFL

=cut
