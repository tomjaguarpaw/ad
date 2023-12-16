# Scrolling the screen down with \ESCM should redraw the bar

echo -ne "FAILURE Should not be able to see this"

for i in $(seq 1 $LINES); do
    echo
done

/usr/bin/echo -ne "\eM"
/usr/bin/echo -ne "v Should be able to see bar here\n"
/usr/bin/echo -ne "FAILURE Should not be able to see this"
/usr/bin/echo -ne "\e[H\eM"

sleep 2
