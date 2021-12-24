for i in $(seq -f "%02g" 1 25) ; do
  if [ "23" = "${i}" ]
  then echo "Day ${i} --- SKIPPED"; continue
  fi
  if [ -e "aoc${i}.v" ]
  then echo "Day ${i}"; ./a.sh aoc${i}.v aoc${i}_input.txt solve12
  fi
done
