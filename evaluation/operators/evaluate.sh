#!/bin/bash

newFails=0
primitiveFails=0

for filename in ./originalTests/*.smt2; do
  echo $filename
  timeout 10 ../../build/bin/cvc5 --solve-int-as-bag $filename > /dev/null 2>&1
  RESULT=$?
  if [ $RESULT -ne 0 ]; then
    echo "$filename - new operators failed"
    echo "$filename" >> "newOperatorsFails.txt"
    ((newFails++))
  fi
done
for filename in ./primitiveTests/*.smt2; do
  echo $filename
  timeout 10 ../../build/bin/cvc5 $filename > /dev/null 2>&1
  RESULT=$?
  if [ $RESULT -ne 0 ]; then
    echo "$filename - primitive failed"
    echo "$filename" >> "primitiveVersionFails.txt"
    ((primitiveFails++))
  fi
done

echo "new operators fails: $newFails"
echo "primitive versions fails: $primitiveFails"