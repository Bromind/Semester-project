CC_ARGS=-g -pg -Wall -Werror

all: c cpp generator

cpp:
	g++ $(CC_ARGS) -std=c++11 map.cpp -o cpp_map

c:
	gcc $(CC_ARGS) map.c main.c -o c_map

generator: 
	gcc $(CC_ARGS) -DGENERATOR main.c map_generator -o c_map_generator

%.png: %.dot
	dot -Tpng $^ -o $@

%.dot: %.gpout
	gprof2dot $^ > $@

%.gpout: % %.gmon.out
	gprof $^ > $@

%.gmon.out: % 
	./$^ test.mapctrl
	mv gmon.out $@

test: all cpp_map.png c_map.png c_map_generator.png test.mapctrl

clean:
	-rm a.out c_map* cpp_map *.o
	-rm *.gmon.out *.gpout *.dot *.png

