#!/bin/bash
NRSPECS="$1"

echo "Timing $NRSPECS specifications..."

for ((i=0; i<$NRSPECS; i++))
do
    echo "Working on spec $((i+1)) of $NRSPECS"
    /usr/bin/time -f "%e" -o timings.txt --append \
         sh -c "nusmv -n $i dice_game_2_players.smv | tail -1 >> specs.txt"
done

