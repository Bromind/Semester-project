#include "map_generator.h"

/*  0 <= initial_position < capacity
 *  gcd(capacity, offset) = 1;
 * */
struct index_generator {
  size_t initial_position;
  size_t offset;
};

#define INITIAL_POSITION_FROM_HASH(hash, capacity) (hash)%(capacity)
#define OFFSET_FROM_HASH(hash, capacity) ((hash)|(1))%(capacity)
#define HASH_EQUALS(h1, h2) (h1.entry_point_hash == h2.entry_point_hash)&&(h1.offset_hash == h2.offset_hash)


static
int loop(int k, int capacity)
{
	int g = k%capacity;
	int res = (g + capacity)%capacity;
	return res;
}

static
int find_key (int* busybits, void** keyps, hash_t* k_hashes, int start,
		void* keyp, map_keys_equality* eq, hash_t key_hash,
		int capacity)
{
  struct index_generator gen = {
    .initial_position = INITIAL_POSITION_FROM_HASH(key_hash.entry_point_hash, capacity),
    .offset = OFFSET_FROM_HASH(key_hash.offset_hash, capacity),
  };

  int i = 0;
  for (; i < capacity; ++i)
  {
    int index = loop(start + i*(gen.offset), capacity);
    int bb = busybits[index];
    hash_t kh = k_hashes[index];
    void* kp = keyps[index];
    if (bb != 0 && HASH_EQUALS(kh, key_hash)) {
      if (eq(kp, keyp)) {
        return index;
      }
    } else {
    }
  }
  return -1;
}

static
int find_empty (int* busybits, int start, struct index_generator gen, int capacity)
{
	int i = 0;
	for (; i < capacity; ++i)
	{
		int index = loop(start + i*(gen.offset), capacity);
		int bb = busybits[index];
		if (0 == bb) {
			return index;
		}
	}
	return -1;
}

void map_initialize (int* busybits, map_keys_equality* eq,
		void** keyps, int* khs, int* vals,
		int capacity)
{
	int i = 0;
	for (; i < capacity; ++i)
	{
		busybits[i] = 0;
	}
}

int map_get (int* busybits, void** keyps, hash_t* k_hashes, int* values,
    void* keyp, map_keys_equality* eq, hash_t hash, int* value,
    int capacity)
{
  struct index_generator gen = {
    .initial_position = INITIAL_POSITION_FROM_HASH(hash.entry_point_hash, capacity),
    .offset = OFFSET_FROM_HASH(hash.offset_hash, capacity),
  };

  int start = loop(gen.initial_position, capacity);
  int index = find_key(busybits, keyps, k_hashes, gen.initial_position,
      keyp, eq, hash, capacity);
  if (-1 == index)
  {
    return 0;
  }
  *value = values[index];
  return 1;
}

int map_put (int* busybits, void** keyps, hash_t* k_hashes, int* values,
    void* keyp, hash_t hash, int value,
    int capacity)
{
  struct index_generator gen = {
    .initial_position = INITIAL_POSITION_FROM_HASH(hash.entry_point_hash, capacity),
    .offset = OFFSET_FROM_HASH(hash.offset_hash, capacity),
  };

  int start = loop(gen.initial_position, capacity);
  int index = find_empty(busybits, start, gen, capacity);
  if (-1 == index)
  {
    return 0;
  }
  busybits[index] = 1;
  keyps[index] = keyp;
  k_hashes[index] = hash;
  values[index] = value;
  return 1;
}

int map_erase (int* busybits, void** keyps, hash_t* k_hashes, void* keyp,
    map_keys_equality* eq, hash_t hash, int capacity,
    void** keyp_out)
{
  struct index_generator gen = {
    .initial_position = INITIAL_POSITION_FROM_HASH(hash.entry_point_hash, capacity),
    .offset = OFFSET_FROM_HASH(hash.offset_hash, capacity),
  };

  int start = loop(gen.initial_position, capacity);
  int index = find_key(busybits, keyps, k_hashes, start,
      keyp, eq, hash, capacity);
  if (-1 == index)
  {
    return 0;
  }
  busybits[index] = 0;
  *keyp_out = keyps[index];
  return 1;
}

int map_size (int* busybits, int capacity)
{
	int s = 0;
	int i = 0;
	for (; i < capacity; ++i)
	{
		if (busybits[i] != 0)
		{
			++s;
		}
	}
	return s;
}
