#!/bin/bash

withFails=0
withoutFails=0

for filename in ./*.smt2; do
  echo "$filename:"
  timeout 10 ../../build/bin/cvc5 --solve-int-as-bag $filename > /dev/null 2>&1
  RESULT=$?
  if [ $RESULT -ne 0 ]; then
    echo "$filename using solveIntAsBag failed"
    echo "$filename - timeout" >> "solveIntAsBagFails.txt"
    ((withFails++))
    timeout 10 ../build/bin/cvc5 $filename > /dev/null 2>&1
    RESULT=$?
    if [ $RESULT -ne 0 ]; then
      echo "$filename without solveIntAsBag failed"
      echo "$filename - timeout" >> "withoutSolveIntAsBagFails.txt"
      ((withoutFails++))
    fi
  else
    timeout 10 ../../build/bin/cvc5 $filename > /dev/null 2>&1
    RESULT=$?
    if [ $RESULT -ne 0 ]; then
      echo "$filename without solveIntAsBag failed"
      echo "$filename - timeout" >> "withoutSolveIntAsBagFails.txt"
      ((withoutFails++))
    else
      OUTPUT1=$(../../build/bin/cvc5 --solve-int-as-bag $filename)
      OUTPUT2=$(../../build/bin/cvc5 $filename)
      echo "first result - ${OUTPUT1}"
      echo "second result - ${OUTPUT2}"
      if [[ "$OUTPUT1" != "$OUTPUT2" ]]; then
        echo "$filename using solveIntAsBag failed"
        echo "$filename - different result" >> "solveIntAsBagFails.txt"
        ((withFails++))
      fi
    fi
  fi
done

echo "solveIntAsBag fails: $withFails"
echo "without solveIntAsBag fails: $withoutFails"