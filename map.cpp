#include <iostream>
#include <assert.h>
#include <fstream>
#include <string>
#include <unordered_map>

#define CONFLICT 5

struct IntHasher
{
  size_t operator() (const int &i) const {
    return i/CONFLICT;
  }
};

clock_t parseFile(std::string filename, std::unordered_map<int, int, IntHasher> map_table)
{
  clock_t total, tmp;

  std::ifstream infile(filename);

  while(! infile.eof()) {
    int key, value;
    std::string operation;
    infile >> operation >> key;
    if (operation == "insert") {
      infile >> value;
      std::cout << "put key " << key << " with value " << value << std::endl;
      tmp = clock();
      map_table[key] = value;
      total += clock() - tmp;
    } else 
      if (operation == "assert") {
        int expected;
        infile >> expected;
        std::cout << "assert key " << key << " has value " << expected << std::endl;
        tmp = clock();
        value = map_table[key];
        total += clock() - tmp;
        assert(expected == value);
      } else 
        if (operation == "delete")
       {
          std::cout << "remove key " << key << std::endl;
          tmp = clock();
          map_table.erase(key);
          total += clock() - tmp;
        } else 
          std::cout << "command is not understood" << std::endl;
  }
  return total;
}

int main(int argc, char* argv[])
{
  if(argc != 2) {
    std::cout << "Usage: " << argv[0] << " testfile" << std::endl;
    return -1;
  }
  std::unordered_map<int, int, IntHasher> map_table;

  clock_t elapsed = parseFile(argv[1], map_table);
std::cout << "Time used for map operations: " << (long double) elapsed*1000/CLOCKS_PER_SEC << "ms" << std::endl;

  return 0;
}

