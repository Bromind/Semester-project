#include "map.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define CAPACITY 10000
#define RANGE CAPACITY
#define CONFLICTS 3

#undef DEBUG
#undef VERBOSE

// For the map table
int *busybit;
void** keyps;
int *khs;
int *vals;

size_t capacity = CAPACITY;
size_t conflict = CONFLICTS;
size_t range = RANGE;

struct myInt {
  int value;
};

clock_t parseFile(const char* filename, struct myInt keys[], size_t capacity);

int compare(void* key1, void* key2)
{
  return ((struct myInt*)key1)->value == ((struct myInt*)key2)->value;
}

int main(int argc, char* argv[])
{
  if(argc < 2)
  {
    fprintf(stderr, "Usage: %s testfile [capacity] [range] [conflicts]\n", argv[0]);
    return -1;
  }
  char* filename = argv[1];
  if(argc >= 3)
    capacity = atoi(argv[2]);
  if(argc >= 4)
    range = atoi(argv[3]);
  if(argc >= 5)
    conflict= atoi(argv[4]);

  busybit = malloc(capacity * sizeof(int));
  keyps = malloc(capacity * sizeof(int*));
  khs = malloc(capacity * sizeof(int));
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

  //return run(keys, 0, 0) == 0;
  clock_t time = parseFile(filename, keys, capacity);
  printf("Time used for map operations: %Lfms\n", (long double) time*1000/CLOCKS_PER_SEC);
  return 0;
}

int hashKey(const struct myInt key)
{
  return (key.value %conflict)%capacity;
}

clock_t put(struct myInt keys[], int key, int value, size_t capacity)
{
  clock_t begin, end;
  begin = clock();
  map_put(busybit, keyps, khs, vals, &keys[key], hashKey(keys[key]), value, capacity);
  end = clock();

  return end - begin;
}

clock_t getAndCheck(struct myInt keys[], int key, int expected, size_t capacity)
{
  clock_t begin, end;
  int value, res;
  begin = clock();
  res = map_get(busybit, keyps, khs, vals, &keys[key], compare, hashKey(keys[key]), &value, capacity);
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
  map_erase(busybit, keyps, khs, &keys[key], compare, hashKey(keys[key]), capacity, (void**) &deleted);
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
  while(EOF != fscanf(file, "%ms %i", &operation, &key))
  {
    if(strncmp(operation, "insert", 6) == 0) {
      int value;
      fscanf(file, "%i \n", &value);
      printf("put key %i with value %i\n", key, value);
      total += put(keys, key, value, capacity);
    } else if(strncmp(operation, "assert", 6) == 0) {
      int expected;
      fscanf(file, "%i \n", &expected);
      if(expected < 0) 
      {
        printf("assert key %i is undefined\n", key);
      } else {
        printf("assert key %i has value %i\n", key, expected);
      }
      total += getAndCheck(keys, key, expected, capacity);
    } else if(strncmp(operation, "remove", 6) == 0) {
      fscanf(file, "\n");
      printf("remove key %i\n", key);
      total += removeKey(keys, key, capacity);
    } else {
      printf("command is not understood: %s\n", operation);
    }
    free(operation);
  }

  fclose(file);
  return total;
}
