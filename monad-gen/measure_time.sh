#!/bin/bash

targets="F G H I St22 St32"
methods="--v1 --v2 --v2-cached"
log_file="./measured_times"
time_format="\"%C\",%U,%e,%Mk"

cabal build monad-gen -O2 || exit 1
for method in $methods; do
  for target in $targets; do
    echo $method $target
    cabal exec -O2 -- /usr/bin/time -a -o "$log_file" -f "$time_format" monad-gen -o ./tmp $method $target
  done
done
