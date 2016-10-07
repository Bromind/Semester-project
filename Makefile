CC_ARGS=-g -pg -Wall -Werror

all: c cpp

cpp:
	g++ $(CC_ARGS) -std=c++11 map.cpp -o cpp_map

c:
	gcc $(CC_ARGS) map.c main.c -o c_map

%.png: %.dot
	dot -Tpng $^ -o $@

%.dot: %.gpout
	gprof2dot $^ > $@

%.gpout: % %.gmon.out
	gprof $^ > $@

%.gmon.out: % 
	./$^
	mv gmon.out $@

test: all cpp_map.png c_map.png

clean:
	-rm a.out c_map cpp_map *.o
	-rm *.gmon.out *.gpout *.dot *.png

