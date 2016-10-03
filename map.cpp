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

void fillTable(std::unordered_map<int, int, IntHasher> map_table)
{
  for(int i = 0; i < CAPACITY; i++)
    map_table[keys[i]] = i;
}

bool getTable(std::unordered_map<int, int, IntHasher> map_table)
{
  bool res = true;
  for(int i = 0; i < CAPACITY; i++)
  {
    res |= map_table[keys[i]] == i;
  }

  return res;
}

bool run(std::unordered_map<int, int, IntHasher> map_table)
{
  bool res = true;
  fillTable(map_table);
  res |= getTable(map_table);
  return res;
}

int main()
{
  int capacity, conflicts;
  std::unordered_map<int, int, IntHasher> map_table;

  initTable();
  bool res = run(map_table);

  if(res)
    return 0;
  else 
    return -1;
}

