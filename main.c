#include "map.h"
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#define CAPACITY 10000
#define CONFLICTS 3

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

  printf("CAPACITY = %d; CONFLICTS = %d\n", capacity, conflict);
  srand(42); // Pseudo random number, deterministic seed for debugging

  // keys initialization
  int *keys = malloc((capacity) * sizeof(int));
  int i = 0;
  for(; i < capacity; i++)
    keys[i] = i;

  run(keys, 0, 0);
}

int run(int* keys, int nb_insert_conflict, int nb_get) 
{
  int n_res = 0;
  clock_t fill_init, fill_end, get;

  map_initialize(busybit, &compare, (void**) keyps, khs, vals, capacity);
  fill_init = clock();
  n_res |= fillTable(keys); // First, fill the table
  fill_end = clock();
  getTable(keys);
  get = clock();

  printf("fill: %f, get: %f\n", ((double)fill_end - fill_init)/CLOCKS_PER_SEC, ((double)get - fill_end)/CLOCKS_PER_SEC);
  return n_res;

}

int hashKey(int key)
{
  return (key%conflict)%capacity;
}

int fillTable(int* keys) 
{ 
  int i = 0;
  int n_resPut = 0;
  for(; i < capacity; ++i)
  {
    n_resPut |= !map_put(busybit, (void**)keyps, khs, vals, &keys[i], hashKey(keys[i]), i, capacity);
  }


  return n_resPut;
}

int getTable(int* keys)
{
  int i = 0, n_resGet = 0;
  for(; i < capacity; ++i)
  {
    int j;
    n_resGet |= !map_get(busybit, (void**)keyps, khs, vals, &keys[i], compare, hashKey(keys[i]), &j, capacity);
    n_resGet |= j == i;
  }
  return n_resGet;
}

