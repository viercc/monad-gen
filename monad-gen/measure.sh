#!/bin/bash

targets="F G H I J K T U V"
log_file="./measured_times"
time_format="\"%C\",%U,%e,%Mk"

cabal build monad-gen || exit 1
for target in $targets; do
  echo $target
  cabal exec -- /usr/bin/time -a -o "$log_file" -f "$time_format" monad-gen $target
done
