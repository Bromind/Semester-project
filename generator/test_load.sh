#!/bin/sh
# Author: Martin Vassor
# Description: Compare the hashmap implementations with different load values
# Creation date: 14-10-2016
# Last modified: Tue Oct 18 13:40:50 2016
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

echo "# conf load_factor time" > load_results_r-"$READ"
echo "# conf: 0 -> default C" >> load_results_r-"$READ"
echo "#       1 -> generator C" >> load_results_r-"$READ"
echo "#       2 -> Default C++" >> load_results_r-"$READ"
echo "#       3 -> C++ with dummy hash function" >> load_results_r-"$READ"

for i in `seq $#`; do
	echo "Generate test file of length $LENGTH, read ratio $READ, and load $1";
	FILE="test_files/l-"$LENGTH"_c-16384_l-"$1"_r-"$READ"-no_contain.mapctrl"
	./generate.sh "$LENGTH" --range=65536 --capacity=16384 --load="$1" --read="$READ" --read-existing-only=true > "$FILE"

        echo "Measure time: ";

	echo "0 $1 $(../c_map "$FILE" | cut -d ':' -f 2 | cut -d 'm' -f 1)" >> load_results_r-"$READ"
	echo "1 $1 $(../c_map_generator "$FILE" | cut -d ':' -f 2 | cut -d 'm' -f 1)" >> load_results_r-"$READ"
	echo "2 $1 $(../cpp_map "$FILE" | cut -d ':' -f 2 | cut -d 'm' -f 1)" >> load_results_r-"$READ"
	echo "3 $1 $(../cpp_map_default "$FILE" | cut -d ':' -f 2 | cut -d 'm' -f 1)" >> load_results_r-"$READ"
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
