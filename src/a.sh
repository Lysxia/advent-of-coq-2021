#!/bin/sh

set -e

if [ "$#" -ne 3 ]; then
  echo -e "Usage: $0 aocXX.v aocXX_input.txt solve"
  echo -e "where"
  echo -e "\taocXX.v\t\tSolution module"
  echo -e "\taocXX_input.txt\tInput file"
  echo -e "\tsolve\t\tSolution function name (usually solve or solve2 or solve12)"
  exit 1
fi

BUILD=build
mkdir -p $BUILD

SOLUTION=$1
INPUT=$2
FUNC=$3
INPUT_=$BUILD/${INPUT%.*}

cat <(echo -e "Require Import ${SOLUTION%.v}. Definition x := input") \
  <(if [ -e $INPUT.prep ]; then ./$INPUT.prep < $INPUT ; else cat $INPUT ; fi) \
  <(echo -e ".\nCompute $FUNC x.") > $INPUT_.v

coqc -R $BUILD aoc $SOLUTION -o $BUILD/${SOLUTION%.v}.vo
coqc -R $BUILD aoc $INPUT_.v -o $INPUT_.vo
