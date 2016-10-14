set terminal pngcairo
set output 'load_results.png'

set style line 1 lc rgb '#0060ad' pi -1 pt 7 ps 1.5 lt 1 lw 2 # --- blue
set style line 2 lc rgb '#60ad00' pi -1 pt 7 ps 1.5 lt 1 lw 2 # --- blue
set style line 3 lc rgb '#ad0060' pi -1 pt 7 ps 1.5 lt 1 lw 2 # --- blue
set style line 4 lc rgb '#00ad60' pi -1 pt 7 ps 1.5 lt 1 lw 2 # --- blue

set pointintervalbox 3

stats 'load_results' using 3 prefix "A"

if (!exists("filename")) filename='load_results'

set title filename

set xrange [0:1]
set yrange [0:1.35*A_max]
set xlabel "Load [percentage]"
set ylabel "Time [ms]"


plot '< grep "^0 .*" load_results' using 2:3 title "C implementation" with linespoints ls 1, \
'< grep "^1 .*" load_results' using 2:3 title "C implementation with offset generator" with linespoints ls 2, \
'< grep "^2 .*" load_results' using 2:3 title "C++ stdlib implementation" with linespoints ls 3, \
'< grep "^3 .*" load_results' using 2:3 title "C++ stdlib implementation with dummy hash function" with linespoints ls 4
