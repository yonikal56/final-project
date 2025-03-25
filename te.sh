#!/bin/bash

# בדיקה אם יש מספיק פרמטרים
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <shared_param>"
    exit 1
fi

SHARED_PARAM=$1

# הגדרת התוכנית והפרמטרים
PROGRAM="./build/bin/cvc5"
PARAM1=("--solve-int-as-bag" "$SHARED_PARAM")
PARAM2=("$SHARED_PARAM")

# הפעלת התוכנית עם שתי קבוצות הפרמטרים
OUTPUT1=$($PROGRAM "${PARAM1[@]}")
OUTPUT2=$($PROGRAM "${PARAM2[@]}")

# בדיקה אם התנאים מתקיימים
if [ "$OUTPUT1" == "unsat" ] && [ "$OUTPUT2" == "sat" ]; then
    echo "a"
else
    echo "b"
fi
