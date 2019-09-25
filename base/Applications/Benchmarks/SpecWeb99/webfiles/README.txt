Here is how to run webfiles:

On Windows:
in Applications\Benchmarks\SpecWeb99\webfiles type
"msb"

On Singularity:

First run:
- "fatcontrol @format /dev/vol2"
- "fatcontrol @mount /dev/vol2 /fs"
- "wafgen99 -v 10 /fs" [Generates lots of files]
- "fatcontrol @unmount"
- reboot to clear the log.

Second boot:
- "fatcontrol @mount /dev/vol2 /fs"
- "webfiles -r:60"

Alternatively, to run an fixed benchmark size, use the -f:X, forced
iteration, parameter:
- "webfiles -f:20000"


