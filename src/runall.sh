for i in $(seq -f "%02g" 1 25) ; do
  if [[ -e "aoc${i}.v" ]] ; then
    echo "Day ${i}"
    if [[ "24" = "${i}" ]]
    then echo "This might take 10 minutes."
    fi
    ./a.sh aoc${i}.v aoc${i}_input.txt solve12
  fi
done
