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

### Performance results

## Implementation

### Function provided

### Internal functions

## Proof

### Overview

### Todo list
