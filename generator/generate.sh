#!/bin/sh
# Author: Martin Vassor
# Description: Generate a payload to test hashmap implementations
# Creation date: 07-10-2016
# Last modified: Tue Oct 25 12:37:30 2016
# Known bugs: 

print_help() {
	echo "Usage: $0 LENGTH [OPTION]"
}

terminate() {
	./Bash-collections/map.sh "$ARGS" remove
	./Bash-collections/map.sh "$MAP" remove
	./Bash-collections/list.sh "$OPS" remove
}

generate_all() {
	# Preload up to target load
	while [ "$(./Bash-collections/map.sh "$MAP" size)" -lt "$(echo "$(./Bash-collections/map.sh "$ARGS" get "load") $(./Bash-collections/map.sh "$ARGS" get "capacity") * 1/p" | dc)" ]; do

          KEY="$(echo "$RANDOM $(./Bash-collections/map.sh "$ARGS" get "range") %p" | dc)"
          if ./Bash-collections/map.sh "$MAP" get "$KEY" > /dev/null; then 
            # if key already exists, remove to avoid different semantics between c++ and verified C
            ./Bash-collections/list.sh "$OPS" append "remove $KEY"
            ./Bash-collections/map.sh "$MAP" delete "$KEY";
          fi;

          NEW_VALUE="$(echo $RANDOM)"
          ./Bash-collections/list.sh "$OPS" append "insert $KEY $NEW_VALUE"
          ./Bash-collections/map.sh "$MAP" put "$KEY" "$NEW_VALUE";
	done;

	./Bash-collections/list.sh "$OPS" append "reset"

	for i in $(seq $(./Bash-collections/map.sh "$ARGS" get length)); do
		generate_single
	done;

	./Bash-collections/list.sh "$OPS" iterate "cat" # >> $(./Bash-collections/map.sh "$ARGS" get "outfile")"
}

generate_single() {
	RW="$(echo "$RANDOM 100 %p" | dc)"
	RW_THRES="$(echo "$(./Bash-collections/map.sh "$ARGS" get "read") 100 * 1/p" | dc)"


	if [ $RW -lt $RW_THRES ]; then
		if [ "$(./Bash-collections/map.sh "$ARGS" get "read-existing-only")" = true ]; then 
			KEY="$(./Bash-collections/map.sh "$MAP" randomKey)"
		else 
			KEY="$(echo "$RANDOM $(./Bash-collections/map.sh "$ARGS" get "range") %p" | dc)"
		fi;
		# Read operation case
		# Try to read the value at $KEY
		if ./Bash-collections/map.sh "$MAP" get "$KEY" >> /dev/null ; then 
			VALUE="$(./Bash-collections/map.sh "$MAP" get "$KEY")"
		else
			VALUE="-1"
		fi;

		./Bash-collections/list.sh "$OPS" append "ensure $KEY $VALUE"
	else 
		# Write operation case
		CURRENT_LOAD="$(./Bash-collections/map.sh "$MAP" size)"
		CAPACITY="$(./Bash-collections/map.sh "$ARGS" get "capacity")"
		TARGET_LOAD="$(echo "$(./Bash-collections/map.sh "$ARGS" get "load") $(./Bash-collections/map.sh "$ARGS" get "capacity") * 1/p" | dc)"
		TRY="$(echo "$RANDOM 100 %p" | dc)"

		KEY="$(echo "$RANDOM $(./Bash-collections/map.sh "$ARGS" get "range") %p" | dc)"

		if [ $CURRENT_LOAD  -gt $TARGET_LOAD ] ; then
			PROBA_REMOVE="$(echo "$CURRENT_LOAD $TARGET_LOAD - 100 * $CAPACITY $TARGET_LOAD - / 2 / 50 +p" | dc )"
		else 
			PROBA_REMOVE="$(echo "$CURRENT_LOAD 100 * $TARGET_LOAD / 2 / p" | dc)"
		fi;
		#echo "Current load: $CURRENT_LOAD, target: $TARGET_LOAD, capacity: $CAPACITY, proba remove: $PROBA_REMOVE, random = $TRY"

		if [ $TRY -lt $PROBA_REMOVE ] ; then
			TO_REMOVE="$(./Bash-collections/map.sh "$MAP" randomKey)"
			./Bash-collections/list.sh "$OPS" append "remove $TO_REMOVE		#current load: $CURRENT_LOAD	target load: $TARGET_LOAD"
			./Bash-collections/map.sh "$MAP" delete "$TO_REMOVE"
		else 
			if ./Bash-collections/map.sh "$MAP" get "$KEY" > /dev/null; then 
			# if key already exists, remove to avoid different semantics between c++ and verified C
				./Bash-collections/list.sh "$OPS" append "remove $KEY"
				./Bash-collections/map.sh "$MAP" delete "$KEY";
			fi;

			NEW_VALUE="$(echo $RANDOM)"
			./Bash-collections/list.sh "$OPS" append "insert $KEY $NEW_VALUE		#current load: $CURRENT_LOAD	target load: $TARGET_LOAD"
			./Bash-collections/map.sh "$MAP" put "$KEY" "$NEW_VALUE";
		fi;
	fi;
}

if [ $# -lt 1 ]; then
	print_help;
	exit -1;
fi

ARGS=$(./Bash-collections/map.sh new)
MAP=$(./Bash-collections/map.sh new)
OPS=$(./Bash-collections/list.sh new)

./Bash-collections/map.sh "$ARGS" put length "$1"
shift

# Put default values
./Bash-collections/map.sh "$ARGS" put "capacity" "50"
./Bash-collections/map.sh "$ARGS" put "read" "0.5"
./Bash-collections/map.sh "$ARGS" put "load" "0.5"
./Bash-collections/map.sh "$ARGS" put "range" "1000"
./Bash-collections/map.sh "$ARGS" put "outfile" "./hashmap_test_file"
./Bash-collections/map.sh "$ARGS" put "read-existing-only" "false"

for i in `seq $#`; do
	ARGNAME=$(echo "$1" | cut -c 3- | cut -d "=" -f1)
	ARGVAL=$(echo "$1" | cut -c 3- | cut -d "=" -f2)
	./Bash-collections/map.sh "$ARGS" put "$ARGNAME" "$ARGVAL"
	shift
done;

generate_all

terminate

: <<=cut

=pod

=head1 NAME

generate.sh - A generator of payload to test hashmap implementations

=head1 SYNOPSIS

C<./generate LENGTH [OPTION]>

=head1 DESCRIPTION

=over 4

=item C<--capacity=capacity> Sets the capacity of the table. Used to compute the average load.

=item C<--range=range> The test will insert values with keys from 0 up to I<range>-1

=item C<--load=load> The target load. Does not guarantee to maintain this load all the time, it tries to achieve it.

=item C<--read=read> Proportion of read request versus write requests.

=item C<--read-existing-only=boolean> Specify whether read operations attempt to read existing key-values only or if it also includes I<contains> operations.

=item C<--outfile=file> Output file

=back

=head1 AUTHOR

Martin Vassor, for DSLab, EPFL

=cut
