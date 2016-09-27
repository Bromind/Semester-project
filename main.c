#include "map.h"
#define CAPACITY 10000000

// For the map table
int busybit[CAPACITY];
int* keyps[CAPACITY];
int khs[CAPACITY];
int vals[CAPACITY];


// keys
int keys[CAPACITY];

int compare(void* key1, void* key2)
{
	return key1 == key2;
}

int main(void)
{
	int i = 0;
	int resPut = 0, resGet = 0;
	map_initialize(busybit, &compare, keyps, khs, vals, CAPACITY);
	for(; i < CAPACITY; ++i)
	{
		keys[i] = i;
		resPut |= !map_put(busybit, keyps, khs, vals, &keys[i], keys[i], i, CAPACITY);
	}

	for(; i < CAPACITY; ++i)
	{
		int j;
		resGet |= !map_get(busybit, keyps, khs, vals, &keys[i], compare, i, &j, CAPACITY);
		resGet |= j == i;
	}

	return resGet || resPut;
}
