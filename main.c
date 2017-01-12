#ifndef GENERATOR
typedef int hash_t;
#include "map.h"
#else
#include "map_generator.h"
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define CAPACITY 16384
#define RANGE (CAPACITY*4)
#define CONFLICTS 3

#undef DEBUG

// For the map table
int *busybit;
void** keyps;
#ifdef GENERATOR
entry_t *khs;
#else
hash_t *khs;
#endif
int *vals;

size_t capacity = CAPACITY;
size_t conflict = CONFLICTS;
size_t range = RANGE;

struct myInt {
  int value;
};

clock_t parseFile(const char* filename, struct myInt keys[], size_t capacity);
#ifdef GENERATOR
entry_t hashKeyEntry(const struct myInt key);
offset_t hashKeyOffset(const struct myInt key);
#else
hash_t hashKey(const struct myInt key);
#endif


int compare(void* key1, void* key2)
{
  return ((struct myInt*)key1)->value == ((struct myInt*)key2)->value;
}

int main(int argc, char* argv[])
{
#ifndef STATIC_TEST
  if(argc < 2)
  {
    fprintf(stderr, "Usage: %s testfile [capacity] [range] [conflicts]\n", argv[0]);
    return -1;
  }
  char* filename = argv[1];
#endif
  if(argc >= 3)
    capacity = atoi(argv[2]);
  if(argc >= 4)
    range = atoi(argv[3]);
  if(argc >= 5)
    conflict= atoi(argv[4]);

  busybit = malloc(capacity * sizeof(int));
  keyps = malloc(capacity * sizeof(int*));
  khs = malloc(capacity * sizeof(hash_t));
  vals = malloc(capacity * sizeof(int));

#ifdef VERBOSE
#ifdef DEBUG
  printf("CAPACITY = %d; CONFLICTS = %d\n", capacity, conflict);
  srand(42); // Pseudo random number, deterministic seed for debugging
#endif
#endif

  // keys initialization
  struct myInt* keys = malloc((range) * sizeof(struct myInt));
  int i = 0;
  for(; i < range; i++)
  {
    keys[i].value = i;
  }

#ifdef STATIC_TEST
int value, res; 
struct myInt* deleted;
clock_t time = clock();

#ifdef GENERATOR

#define remove(x) \
  map_erase(busybit, keyps, khs, &keys[(x)], compare, hashKeyEntry(keys[(x)]), hashKeyOffset(keys[(x)]), capacity, (void**) &deleted)
#define insert(x, y) \
  map_put(busybit, keyps, khs, vals, &keys[(x)], hashKeyEntry(keys[(x)]), hashKeyOffset(keys[(x)]), (y), capacity)

#define ensure(x, y) \
  res = map_get(busybit, keyps, khs, vals, &keys[(x)], compare, hashKeyEntry(keys[(x)]), hashKeyOffset(keys[(x)]), &value, capacity); \
  if((y) < 0) /* Case not expected to be in the map */ \
  { \
    assert(res == 0); \
  } else { \
    assert((value == (y) )); \
  }

#else

#define remove(x) \
  map_erase(busybit, keyps, khs, &keys[(x)], compare, hashKey(keys[(x)]), capacity, (void**) &deleted)
#define insert(x, y) \
  map_put(busybit, keyps, khs, vals, &keys[(x)], hashKey(keys[(x)]), (y), capacity)

#define ensure(x, y) \
  res = map_get(busybit, keyps, khs, vals, &keys[(x)], compare, hashKey(keys[(x)]), &value, capacity); \
  if((y) < 0) /* Case not expected to be in the map */ \
  { \
    assert(res == 0); \
  } else { \
    assert((value == (y) )); \
  }
#endif

#define reset \
  time = clock();

#include "static_test"

time = clock() - time;

#else 
  //return run(keys, 0, 0) == 0;
  clock_t time = parseFile(filename, keys, capacity);
#endif
  printf("Time used for map operations: %Lfms\n", (long double) time*1000/CLOCKS_PER_SEC);
  return 0;
}

#ifndef GENERATOR
hash_t hashKey(const struct myInt key)
{
  return (key.value %conflict)%capacity;
}
#else
entry_t hashKeyEntry(const struct myInt key)
{
  return key.value;
}

offset_t hashKeyOffset(const struct myInt key)
{
    return ((key.value*3%(capacity+1))*7)%capacity; // Somehow mix them, obviously not perfect, but better than nothing.
}
#endif

clock_t put(struct myInt keys[], int key, int value, size_t capacity)
{
  clock_t begin, end;
  begin = clock();
#ifdef GENERATOR
  map_put(busybit, keyps, khs, vals, &keys[key], hashKeyEntry(keys[key]), hashKeyOffset(keys[key]), value, capacity);
#else
  map_put(busybit, keyps, khs, vals, &keys[key], hashKey(keys[key]), value, capacity);
#endif
  end = clock();

  return end - begin;
}

clock_t getAndCheck(struct myInt keys[], int key, int expected, size_t capacity)
{
  clock_t begin, end;
  int value, res;
  begin = clock();
#ifdef GENERATOR
  res = map_get(busybit, keyps, khs, vals, &keys[key], compare, hashKeyEntry(keys[key]), hashKeyOffset(keys[key]), &value, capacity);
#else 
  res = map_get(busybit, keyps, khs, vals, &keys[key], compare, hashKey(keys[key]), &value, capacity);
#endif
  if(expected < 0) // Case not expected to be in the map
  {
    assert(res == 0);
  } else {
    assert((value == expected));
  }
  end = clock();
  return end - begin;
}

clock_t removeKey(struct myInt keys[], int key, size_t capacity)
{
  clock_t begin, end;
  struct myInt* deleted;
  begin = clock();
#ifndef GENERATOR
  map_erase(busybit, keyps, khs, &keys[key], compare, hashKey(keys[key]), capacity, (void**) &deleted);
#else
  map_erase(busybit, keyps, khs, &keys[key], compare, hashKeyEntry(keys[key]), hashKeyOffset(keys[key]), capacity, (void**) &deleted);
#endif
  end = clock();
  return end - begin;
}

clock_t parseFile(const char* filename, struct myInt keys[], size_t capacity)
{
  clock_t total = 0;
  FILE* file;
  file = fopen(filename, "r");
  char* operation;
  int key;
  char dump_line = 0;
  while(EOF != fscanf(file, "%ms", &operation))
  {
    dump_line = 0;
    if(strncmp(operation, "reset", 5) == 0) {
#ifdef VERBOSE
      printf("Reset timer\n");
#endif
      total = 0;
    } else 
      if(EOF != fscanf(file, "%i", &key)) {
        if(strncmp(operation, "insert", 6) == 0) {
          int value;
          if(fscanf(file, "%i", &value) == EOF){
            perror(NULL);
          }
#ifdef VERBOSE
          printf("put key %i with value %i\n", key, value);
#endif
          total += put(keys, key, value, capacity);
        } else if(strncmp(operation, "assert", 6) == 0) {
          int expected;
          if(fscanf(file, "%i", &expected) == EOF) {
            perror(NULL);
          }
#ifdef VERBOSE
          if(expected < 0) 
          {
            printf("assert key %i is undefined\n", key);
          } else {
            printf("assert key %i has value %i\n", key, expected);
          }
#endif
          total += getAndCheck(keys, key, expected, capacity);
        } else if(strncmp(operation, "remove", 6) == 0) {
#ifdef VERBOSE
          printf("remove key %i\n", key);
#endif
          total += removeKey(keys, key, capacity);
        } else {
#ifdef VERBOSE
          printf("command is not understood: %s\n", operation);
#endif
        }
      }
    while(fscanf(file, "%c", &dump_line) != EOF && dump_line != '\n');
    
    free(operation);
  }

  fclose(file);
  return total;
}
