#!/bin/bash

for f in euphony/*.sl; do
	STARTTIME=$(date +%s%N)
	out=`timeout 600 /c/users/shrad/downloads/cvc4-1.7-win64-opt.exe $f`
	retval=$?
	ENDTIME=$(date +%s%N)
	echo "$f,$retval,$((($ENDTIME - $STARTTIME)/1000000000))"
	if [ $retval = 0 ]; then
		echo $out | tr '\r' '\n' | awk 'END{print}'
	fi
done