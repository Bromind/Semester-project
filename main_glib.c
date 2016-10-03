#include <glib.h>
#define CAPACITY 10000
#define CONFLICT 3

int capacity = CAPACITY;
int conflict = CONFLICT;
GHashTable * map_table;

gboolean compare(gconstpointer key1, gconstpointer key2)
{
  if (key1 == key2)
    return TRUE;
  else return FALSE;
}

guint hashKey(gconstpointer key)
{
  return (guint) (key%conflict)%capacity;
}

int main(int argc, char* argv[])
{
  if(argc >= 2)
    capacity = atoi(argv[1]);
  if(argc >= 3)
    conflict = atoi(argv[2]);

#ifdef VERBOSE
  printf("CAPACITY = %d; CONFLICTS = %d\n", capacity, conflict);
#endif

  map_table = g_hash_table_new(hashKey, compare);
  int *keys = malloc((capacity) * sizeof(int));
  int *values = malloc((capacity) * sizeof(int));
  int i = 0;

  for(; i < capacity; i++)
  {
    keys[i] = i;
    values[i] = i;
  }

  return run(keys, 0, 0) == 0;
}

gboolean fillTable(int* keys, int* values) 
{ 
  int i = 0;
  gboolean resPut = TRUE;
  for(; i < capacity; ++i)
  {
    resPut &= g_hash_table_insert(map_table, &keys[i], &values[i]);
  }

  return resPut;
}

gboolean getTable(int* keys, int* values)
{
  int i = 0;
  gboolean resGet = TRUE;
  for(; i < capacity; ++i)
  {
    gpointer j;
    j = g_hash_table_lookup(map_table, &keys[i]);
    resGet &= j == &values[i];
  }
  return resGet;
}

