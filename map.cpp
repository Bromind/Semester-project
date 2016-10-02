#include <iostream>
#include <string>
#include <unordered_map>

#define CONFLICT 3
#define CAPACITY 10000

struct IntHasher
{
  size_t operator() (const int &i) const {
    return i/CONFLICT;
  }
};

int keys[CAPACITY];

inline void initTable(void)
{
  for(int i = 0; i < CAPACITY; i++)
    keys[i]= i;
}

void run(std::unordered_map<int, int, IntHasher> map_table)
{
  for(int i = 0; i < CAPACITY; i++)
    map_table[keys[i]] = i;

}

int main()
{
  int capacity, conflicts;
  std::unordered_map<int, int, IntHasher> map_table;

  initTable();
  run(map_table);

  return 0;
}

