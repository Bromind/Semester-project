#ifndef _MAP_GENERATOR_H_INCLUDED_
#define _MAP_GENERATOR_H_INCLUDED_
#include <stdlib.h>
typedef int map_keys_equality (void* k1, void* k2);

struct hash_value {
  size_t entry_point_hash;
  size_t offset_hash;
};


typedef struct hash_value hash_t;

void map_initialize (int* busybits, map_keys_equality* cmp,
    void** keyps, int* khs, int* vals,
    int capacity);

int map_get (int* busybits, void** keyps, struct hash_value* k_hashes, int* values,
    void* keyp, map_keys_equality* eq, struct hash_value hash, int* value,
    int capacity);

int map_put (int* busybits, void** keyps, struct hash_value* k_hashes, int* values,
    void* keyp, struct hash_value hash, int value,
    int capacity);

int map_erase (int* busybits, void** keyps, struct hash_value* k_hashes, void* keyp,
    map_keys_equality* eq, struct hash_value hash, int capacity,
    void** keyp_out);

int map_size (int* busybits, int capacity);

#endif //_MAP_GENERATOR_H_INCLUDED_
