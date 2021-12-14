for i in $(seq -f "%02g" 1 14) ; do
  echo "Day ${i}"; ./a.sh aoc${i}.v solve12 aoc${i}_input.txt
done
