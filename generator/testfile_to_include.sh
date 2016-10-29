#!/bin/sh
# Author: Martin Vassor
# Description: 
# Creation date: 25-10-2016
# Last modified: Fri Oct 28 15:12:31 2016
# Known bugs: 

print_help() {
	echo "Usage: $0 input_file output_file"
	exit -1;
}

if [ ! $# -eq 2 ]; then 
	print_help;
fi;

sed -e 's/assert/ensure/' -e 's/\([a-z]*\) \([0-9]*\) \(-\?[0-9]*\)/\1(\2, \3);/' -e 's/^\([a-z]*\) \([0-9]*\)/\1(\2);/' -e 's/#\(.*$\)/\/*\1*\//' $1 > $2

: <<=cut

=pod

=head1 NAME

=head1 SYNOPSIS

=head1 AUTHOR

=cut
