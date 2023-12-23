# Wrapnext shouldn't be changed if we emit an escape code that doesn't
# move the cursor

for i in $(seq 1 $LINES); do
    echo
done

echo "Should see both < > and X not overlapping the bar"

/usr/bin/echo -n "<"
for i in `seq 2 $[COLUMNS-1]`; do
    /usr/bin/echo -n " "
done
/usr/bin/echo -n -e ">\e[mX"
sleep 2
