#include <iostream>
#include <limits>
#include <cmath>
#include <assert.h>
#include <fstream>
#include <string>
#include <unordered_map>

#define CONFLICT 5

struct IntHasher
{
  size_t operator() (const int &i) const {
    return i;
  }
};

#ifdef DEFAULT_HASH
clock_t parseFile(std::string filename, std::unordered_map<int, int> map_table)
#else
clock_t parseFile(std::string filename, std::unordered_map<int, int, IntHasher> map_table)
#endif
{
  clock_t total = 0, tmp;

  std::ifstream infile(filename);

  while(! infile.eof()) {
    int key, value;
    std::string operation;
    infile >> operation;
    if (operation == "reset") {
#ifdef VERBOSE
          std::cout << "Reset timer" << std::endl;
#endif
          total = 0;
    } else {
      infile >> key;
      if (operation == "insert") {
        infile >> value;
#ifdef VERBOSE
        std::cout << "put key " << key << " with value " << value << std::endl;
#endif
        tmp = clock();
        map_table[key] = value;
        total += clock() - tmp;
      } else 
        if (operation == "assert") {
          int expected;
          infile >> expected;
          tmp = clock();
          value = map_table[key];
          total += clock() - tmp;
          if(expected >= 0) {
#ifdef VERBOSE
            std::cout << "assert key " << key << " has value " << expected << std::endl;
#endif
            assert(expected == value);
          } else {
#ifdef VERBOSE
            std::cout << "assert key " << key << " is undefined" << std::endl;
#endif
          }
        } else 
          if (operation == "remove")
          {
#ifdef VERBOSE
            std::cout << "remove key " << key << std::endl;
#endif
            tmp = clock();
            map_table.erase(key);
            total += clock() - tmp;
          } else {
#ifdef VERBOSE
              std::cout << "command is not understood: " << operation << std::endl;
#endif
            }
    }

    infile.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
    bool v= infile.eof();
     v= v;
  }
  return total;
}

int main(int argc, char* argv[])
{
#ifndef STATIC_TEST
  if(argc != 2) {
    std::cout << "Usage: " << argv[0] << " testfile" << std::endl;
    return -1;
  }
#endif
#ifdef DEFAULT_HASH
  std::unordered_map<int, int> map_table;
#else
  std::unordered_map<int, int, IntHasher> map_table;
#endif

  map_table.max_load_factor(INFINITY);

#ifdef STATIC_TEST
  clock_t time = clock();
#define remove(x) \
  map_table.erase((x))
#define insert(x, y) \
  map_table[(x)] = (y)
#define ensure(x, y) \
  if ((y) >= 0) \
    assert(map_table[(x)] == (y)); 
#define reset \
  time = clock();

#include "static_test"
  clock_t elapsed = clock() - time;
#else
  clock_t elapsed = parseFile(argv[1], map_table);
#endif
std::cout << "Time used for map operations: " << (long double) elapsed*1000/CLOCKS_PER_SEC << "ms" << std::endl;

  return 0;
}

