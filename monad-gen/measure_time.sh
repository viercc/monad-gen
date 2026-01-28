#!/bin/bash
set -e

bin_dir="./tmp-bin"
monad_gen_cmd="${bin_dir}/monad-gen"

targets="F G H I T_112 complex/V2Maybe St22 St32"
methods="--v1 --v2 --v2-cached"

out_dir="./tmp"
log_file="./measured_times__$(date -Iseconds)"
time_format="\"%C\",%U,%e,%Mk"

cabal build monad-gen -O2 || exit 1
mkdir -p "$bin_dir" && cabal install "--installdir=$bin_dir" --overwrite-policy=always monad-gen -O2
for target in $targets; do
  for method in $methods; do
    echo $target $method
    /usr/bin/time -a -o "$log_file" -f "$time_format" "$monad_gen_cmd" -o "$out_dir" $target $method
  done
done
