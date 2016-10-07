#!/bin/sh
# Author: Martin Vassor
# Description: Download dependancies for the load generator
# Creation date: 07-10-2016
# Last modified: Fri Oct  7 17:36:20 2016
# Known bugs: 

print_help() {
	echo "Usage: $0"
}

wget https://github.com/Bromind/Bash-collections/archive/master.zip \
&& unzip master.zip \
&& rm master.zip \
&& mv Bash-collections-master Bash-collections

: <<=cut

=pod

=head1 NAME

dependancies.sh - Download dependancies for the laod generator

=head1 SYNOPSIS

C<./dependancies.sh>

=head1 AUTHOR

Martin Vassor, for DSLab, EPFL

=cut
