for i in $(seq -f "%02g" 1 25) ; do
  if [[ -e "aoc${i}.v" ]] ; then
    CMD="./a.sh aoc${i}.v aoc${i}_input.txt solve12"
    if [[ "23" = "${i}"  ]]
    then echo "Day ${i} --- SKIPPED (Part 2 goes OOM) --- ${CMD}"; continue
    elif [[ "24" = "${i}" ]]
    then echo "Day ${i} --- SKIPPED (8 minute wait)   --- ${CMD}"; continue
    fi
    echo "Day ${i}"; ${CMD}
  fi
done
