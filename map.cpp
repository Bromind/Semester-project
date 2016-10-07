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

void parseFile(std::string filename, std::unordered_map<int, int, IntHasher> map_table)
{
  std::ifstream infile(filename);

  while(! infile.eof()) {
    int key, value;
    std::string operation;
    infile >> operation >> key;
    if (operation == "insert") {
      infile >> value;
      std::cout << "put key " << key << " with value " << value << std::endl;
      map_table[key] = value;
    } else 
      if (operation == "assert") {
        infile >> value;
        std::cout << "assert key " << key << " has value " << value << std::endl;
        assert(map_table[key] == value);
      } else 
        if (operation == "delete")
       {
          std::cout << "remove key " << key << std::endl;
          map_table.erase(key);
        } else 
          std::cout << "command is not understood" << std::endl;

  }
}

int main(int argc, char* argv[])
{
  if(argc != 2) {
    std::cout << "Usage: " << argv[0] << " testfile" << std::endl;
    return -1;
  }
  std::unordered_map<int, int, IntHasher> map_table;

  parseFile("/tmp/test.mapctrl", map_table);

  return 0;
}

