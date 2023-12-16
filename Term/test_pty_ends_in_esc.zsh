# If we get an `\ESC` then we need to wait for more input rather than
# just treating it as a character.

for i in $(seq 1 $LINES); do
    echo
done

echo "Shouldn't see anything between here"
/usr/bin/echo -n "v"
for i in `seq 2 $[COLUMNS]`; do
    /usr/bin/echo -n " "
done
/usr/bin/echo -n -e "\e"
/usr/bin/echo -n -e "[m"
echo "\n^ and here"

sleep 2
