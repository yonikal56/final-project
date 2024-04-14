#!/bin/bash

for filename in ./intToBag/**/*.smt2; do
  echo "$filename result using solveIntAsBag:"
  timeout 10 ../build/bin/cvc5 --solve-int-as-bag $filename
  echo "$filename result without solveIntAsBag:"
  timeout 10 ../build/bin/cvc5 $filename
done