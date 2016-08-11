#!/usr/bin/env bash

# echo "<!-- FILE AUTOMATICALLY GENERATED FROM '$1'. -->" > $2
# echo "<!-- DO NOT MODIFY THIS FILE MANUALLY! -->" >> $2
# echo >> $2

cat $1 | sed 's/(\*\*//g' | sed 's/\*\*)//g' > $2
