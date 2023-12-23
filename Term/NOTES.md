# Notes

### Automatic margins and newline glitch

It's tempting to turn `am` and `xenl` off because cursor position
tracking becomes simpler and because it's compatible with `readline`
on terminals with `am` and `xenl` on!  However, this is a forlorn
hope.  We want `am`, of course, otherwise simple non-terminal-aware
utilities like `cat` won't work properly.  If we have `am` we probably
ought to turn on `xenl` because that's what all the popular terminals
do (`screen`, `tmux`, `xterm`, `rxvt`, ...).

# TODO

* Account for UTF-8 characters properly
  * [X] width 1
  * [ ] width 2 (xterm renders these as width 2 ([full
        width](https://en.wikipedia.org/wiki/Halfwidth_and_fullwidth_forms))
        forms: 🎄, 🎅, 🏻, but not this: ⓐ)

* Present our terminal type to clients
  * [ ] Choose a name for the terminal type
  * [X] Set `TERM`
  * [X] Encourage users to run `tic smy` (or whatever name we choose)
* Check the host terminal type
  * [X] Warn if it's not `screen`
  * [ ] Expand support to all terminals by using terminfo

# Known issues

`dircolors` (used for telling `ls` which colors to use) doesn't work
with terminal types it does not know.  For some reason it doesn't use
`terminfo`.
