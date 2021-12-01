#!/bin/sh

set -e

if [ "$#" -ne 3 ]; then
  echo "Usage: $0 aocXX.v solve aocXX_input.txt"
  echo "\twhere"
  echo "\t\taocXX.v\t\tSolution module"
  echo "\t\tsolve\t\tSolution function name (usually solve or solve2)"
  echo "\t\taocXX_input.txt\tInput file"
  exit 1
fi

BUILD=build
mkdir -p $BUILD

SOLUTION=$1
FUNC=$2
INPUT=$3
INPUT_=$BUILD/${INPUT%.*}

cat <(echo -e "Require Import ${SOLUTION%.v}. Definition x := input") \
  $INPUT \
  <(echo ". Compute $FUNC x.") > $INPUT_.v

coqc -R $BUILD aoc $SOLUTION -o $BUILD/${SOLUTION%.v}.vo
coqc -R $BUILD aoc $INPUT_.v -o $INPUT_.vo
