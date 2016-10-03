#include "map.h"
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#define CAPACITY 10000
#define CONFLICTS 3

#undef DEBUG
#undef VERBOSE

// For the map table
int *busybit;
int** keyps;
int *khs;
int *vals;

unsigned int capacity = CAPACITY;
unsigned int conflict = CONFLICTS;

int compare(void* key1, void* key2)
{
  return key1 == key2;
}

int main(int argc, char* argv[])
{
  if(argc >= 2)
    capacity = atoi(argv[1]);
  if(argc >= 3)
    conflict = atoi(argv[2]);

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
  int *keys = malloc((capacity) * sizeof(int));
  int i = 0;
  for(; i < capacity; i++)
    keys[i] = i;

  return run(keys, 0, 0) == 0;
}


/* Returns 1 if O.K., 0 o/w */
int run(int* keys, int nb_insert_conflict, int nb_get) 
{
  int res = 1;
#ifdef DEBUG
  clock_t fill_init, fill_end, get;
#endif

  map_initialize(busybit, &compare, (void**) keyps, khs, vals, capacity);
#ifdef DEBUG
  fill_init = clock();
#endif
  res &= fillTable(keys); // First, fill the table
#ifdef DEBUG
  fill_end = clock();
#endif
  res &= getTable(keys);
#ifdef DEBUG
  get = clock();
#ifdef VERBOSE
  printf("fill: %f, get: %f\n", ((double)fill_end - fill_init)/CLOCKS_PER_SEC, ((double)get - fill_end)/CLOCKS_PER_SEC);
#endif
#endif
  return res;

}

int hashKey(int key)
{
  return (key%conflict)%capacity;
}

int fillTable(int* keys) 
{ 
  int i = 0;
  int resPut = 1;
  for(; i < capacity; ++i)
  {
    resPut &= map_put(busybit, (void**)keyps, khs, vals, &keys[i], hashKey(keys[i]), i, capacity);
  }


  return resPut;
}

int getTable(int* keys)
{
  int i = 0, resGet = 1;
  for(; i < capacity; ++i)
  {
    int j;
    resGet &= map_get(busybit, (void**)keyps, khs, vals, &keys[i], compare, hashKey(keys[i]), &j, capacity);
    resGet &= j == i;
  }
  return resGet;
}

