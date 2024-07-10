#!/bin/bash

withFails=0
withoutFails=0

for filename in ./intToBag/**/*.smt2; do
  echo "$filename:"
  timeout 10 ../build/bin/cvc5 --solve-int-as-bag $filename > /dev/null 2>&1
  RESULT=$?
  if [ $RESULT -ne 0 ]; then
    echo "$filename using solveIntAsBag failed"
    echo "$filename" >> "solveIntAsBagFails.txt"
    ((withFails++))
  fi
  timeout 10 ../build/bin/cvc5 $filename > /dev/null 2>&1
  RESULT=$?
  if [ $RESULT -ne 0 ]; then
    echo "$filename without solveIntAsBag failed"
    echo "$filename" >> "withoutSolveIntAsBagFails.txt"
    ((withoutFails++))
  fi
done

echo "solveIntAsBag fails: $withFails"
echo "without solveIntAsBag fails: $withoutFails"