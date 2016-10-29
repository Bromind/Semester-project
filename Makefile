CC_ARGS=-O3 -Wall -Werror -DSTATIC_TEST

all: static_test c cpp c_generator cpp_default

cpp:
	g++ $(CC_ARGS) -std=c++11 map.cpp -o cpp_map

cpp_default:
	g++ $(CC_ARGS) -std=c++11 -DDEFAULT map.cpp -o cpp_map_default

c:
	gcc $(CC_ARGS) map.c main.c -o c_map

c_generator: 
	gcc $(CC_ARGS) -DGENERATOR main.c map_generator.c -o c_map_generator

%.png: %.dot
	dot -Tpng $^ -o $@

%.dot: %.gpout
	gprof2dot $^ > $@

%.gpout: % %.gmon.out
	gprof $^ > $@

%.gmon.out: % 
	./$^ test.mapctrl
	mv gmon.out $@

test: all cpp_map.png c_map.png c_map_generator.png cpp_map_default.png test.mapctrl

clean:
	-rm a.out c_map* cpp_map* *.o
	-rm *.gmon.out *.gpout *.dot *.png
