#!/bin/bash

for filename in ./intToBag/*; do
  echo "$filename result using solveIntAsBag:"
  time ../build/bin/cvc5 --solve-int-as-bag $filename
  echo "$filename result without solveIntAsBag:"
  time ../build/bin/cvc5 $filename
done