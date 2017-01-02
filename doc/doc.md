# Double-hashing hash-table

## Introduction

This document is a short synthesis of the semester project I am doing at DSLab, EPFL. A complete report will eventually be uploaded.

## Files & Build instruction

### Files

| File/Directory | Description |
| --- | --- |
| generator/ | Folder containing the performance benchmark generation & measurement |
| Makefile | makefile of the project (see "Build instruction") |
| arith.gh | Multiplication lemmas |
| chinese_remainder_th.gh | Proof of the Chinese remainder theorem & associated lemmas | 
| main.c | Common main file for performance evaluation, for both original and double-hashing versions | 
| map.c | Original implementation |
| map.h | Original implementation header file |
| map_generator.c | Double-hashing implementation |
| map_generator.h | Double-hashing header file |
| modulo.gh | modulo & other lemmas |
| nthProp.gh | lemmas for iterating over list (up_to lemma) |
| stdex.gh | some standard lemmas |

### Build instructions

To build the benchmarks, run `make all`. To compile individual binaries, use the `GENERATOR` macro. If it is defined, `main.c` will be preprocessed to use `map_generator.h` header instead of  `map.h`.

## Double-hashing behaviour

Double-hashing is a collision resolution method for open-addressing hash tables. 

### Open-addressing

Opposed to separated chaining, in open-addressing, the buckets of the table directly contain the data to record. In separate chaining, each bucket contains a reference to a list containing all data which have the same hash.

### Double-hashing

A naive way to implement a collision resolution mechanism for open-addressing tables is to insert data at the first empty bucket after the hash of the data. However, when multiple collision occur for the same hash, each insertion collide with all previously inserted data. 

Double-hashing sole this problem by using an independent second hash function to compute the offset. Hence, if three insertions collide (i.e. h1(i1) == h1(i2) == h1(i3)), i1 will be placed in the cell h1(i1), i2 in h1(i2) + h2(i2) and i3 in h1(i3) + h2(i3). Since there is very low probability that both h1(i2) ==  h1(i3) *and* h2(i2) == h2(i3), one collision is avoided.

## Performance

### Performance evaluation methodology

The different implementations are tested with randomly generated access sequences. Different parameters are adjustable: 
 * The size of the map
 * The length of the sequence (i.e. the number of accesses)
 * The range of the key inserted
 * The target load of the map
 * The proportion of read access and write accesses
 * Whether the test tries to access data not in the table (test for existence)

The generated test contains two parts: 
 1. A warm-up step, in which data is inserted until the target load is reached
 2. A timed step, in which *n* accesses are done, where *n* is the given length

Given a probability *p* of doing a read access, write accesses are done with probability *1-p*. If a write access is done, it is either an insertion or a deletion. The probability of each is computed in function of the current load.

### Performance evaluation *How to* ?

The evaluation works in three steps. 
 1. Generate `mapctrl` files. Those are files which contains a sequence of controls for map. 
 2. Convert the `mapctrl` into includable files. 
 3. Compile the different implementations.
 4. Synthesize the results into graph plots. 

The script `test_load.sh` run all these steps. As generating files is quite long, editing and commenting a line in this script allows to reuse previously generated files.

In the current state, the script reuses the files in the `test_files` folder.

### Performance results

The relevant performance graph are in the sub-directories `load_test_contains` and `load_test_wo_contains`. These folders contain both graphs and numerical data. One can see that the time used by the double-hash table is almost always comparable to the C++ standard implementation. 

In particular, when only existing data is accessed (do not test for existence), the performance are always better than C++.

## Implementation

### Function provided

### Internal functions

## Proof

### Overview

### Todo list
