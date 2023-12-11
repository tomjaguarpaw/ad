# Notes

### Automatic margins and newline glitch

It's tempting to turn `am` and `xenl` off because cursor position
tracking becomes simpler and because it's compatible with `readline`
on terminals with `am` and `xenl` on!  However, this is a forlorn
hope.  We want `am`, of course, otherwise simple non-terminal-aware
utilities like `cat` won't work properly.  If we have `am` we probably
ought to turn on `xenl` because that's what all the popular terminals
do (`screen`, `tmux`, `xterm`, `rxvt`, ...).
