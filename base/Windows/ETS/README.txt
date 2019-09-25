Event Tracing for Singularity (ETS)
-----------------------------------

* What 

Lightweight event tracing for performance monitoring and debugging.


* How

Just like ETW (Event Tracing for Windows):
http://msdn.microsoft.com/library/default.asp?url=/library/en-us/perfmon/base/event_tracing.asp

Events are posted from all over the codebase by using calls of the
form:

Monitoring.Log(PROVIDER, TYPE, ARGs...)

This logs an event to a circular buffer in kernel memory.  Currently
this is 4MB, split into 3MB for regular events and 1MB for text
strings.  Size is controlled by MONITORING_BUFFER_SIZE etc in
Kernel/Native/Monitoring.cpp

PROVIDER is a member of the Monitoring.Providers enum which allows
several bits of code to post events without needing to negotiate
unique event IDs.  Each provider defines their own event TYPEs (as
ushorts), which are typically from an enum near the top of each
provider's code, eg ThreadEvent in Thread.cs.

A full listing of all providers together with their events is given in
TMF format as "singularity.tmf" in this directory.  A thinned out set
of events (mainly ignoring WaitHandle synchronisation) is documented
in "singularity-lite.tmf".

These files are used by the parser "mag_ets.exe" (in build/ directory)
to decode the binary packed event format.

Use Applications/Network/MonNet to export the current contexts of the
kernel's log buffer out over the network to your workstation (eg
10.99.99.1) for analysis and visualisation.


* Sample usage

Build, ie do an "msb" from:
1. A distro such as Distro\BVT.proj.
2. Applications\Network
3. Applications\Network\MonNet
3b. <anything else you need>
4. Distro

Run:
1. Boot singularity
1b. run your experiment
2. netstack &
3. ipconfig /dev/nic0 10.99.99.2 255.255.255.0 10.99.99.1
4. run netcat (or equivalent) on your workstation:
     nc -l -p 5000 >justboot.ets  # ie listen for TCP connection on port 5000
5. monnet 10.99.99.1 5000

Analyse:
1. To dump as CSV an .ets file:
    mag_ets --tracerpt -t Windows\ETS\singularity.tmf -e justboot.ets -o justboot.csv

Sample run:
Parsing TMF ...
    ... Windows\ETS\singularity.tmf
...done
Parsing Contract Message Tag mapfiles ...
...done
........................................................
Stats:
Processed 0 buffers, 56231 events
Dropped 0 events, 64 unknown events
Unknown event types (guid, version, type):
('20', 0, 11) 64


2. To parse .ets file for visualisation or request extraction:
    mag_ets -t Windows\ETS\singularity-lite.tmf -c Contracts\obj\Debug.MarkSweep\__All.Contracts.tmf -e justboot.ets -o justboot.vis

Sample run:
Parsing TMF ...
    ... ..\..\Windows\ETS\singularity-lite.tmf
...done
Parsing Contract Message Tag mapfiles ...
    ... ..\..\Contracts\obj\Debug.MarkSweep\__All.Contracts.tmf
...done
Writing visualisation output to justboot.vis
.........................................Found Shell event: 'netstack &' at time
: 1079855362440
.........Found Shell event: 'ipconfig /dev/nic0 10.99.99.2 255.255.255.0 10.99.9
9.1' at time: 1106483455418
......
Stats:
Processed 0 buffers, 56231 events
Dropped 0 events, 13209 unknown events
Unknown event types (guid, version, type):
('12', 0, 2) 289
('10', 0, 10) 3953
('11', 0, 2) 5579
('20', 0, 11) 64
('13', 0, 2) 9
('11', 0, 1) 31
('9', 0, 2) 89
('9', 0, 1) 3195
Found Shell event: 'monnet 10.99.99.1 5000' at time: 1121610922437
Found 0 requests


3. to visualise .vis file:
    magpyvis justboot.vis
   See below for mini-guide to magpyvis.


If you have events related to private contracts, you will need to
manually generate a .tmf file to describe it.  If you built the
contract into a DLL, this can be done by going:
  nmake FOO.tmf
in the same directory as FOO.dll.  Then pass an extra "-c FOO.tmf"
option to mag_ets when generating the .vis file.


If you want to modify the parser or visualiser, you will need to have
a working Python installation.  You can then download the latest
version of the Magpie toolkit from:
  http://teamemea/sites/cambridge/projects/magpie/


* Contract names and message tag names

The contract names are queried from the runtime type system by MonNet
just before it dumps the .ets file over the network.  It does this in
a really gorey manner by getting the typeof() all the contracts it
knows about.  This clearly should be fixed, but needs support from the
typesystem.

The message names are got by running ILDASM over the contract DLLs
just after they are built and using an awk script to generate .tmf
from the Tags enum each contract has.  This needs a GAWK.EXE in your
build/ directory, but at this time I am not checking one in.  There is
a gawk.cmd placeholder reminding you of this which will be used
instead of gawk.exe.


* Mini-guide to magpievis

On x-axis is time, on y-axis are various resources like threads, CPUs,
IRQs, channels, waithandles.  Vertical lines are labelled events which
happened at some time, and are bound to the resources they used. Fat
blue lines join contract send and receive events together.

Left-click near an event pops up a tooltip giving the event's
timestamp, and all its attributes together with their binding mode
(NONE, BASIC, START, STOP).  Left-click also sets the "current
timestamp" to the location clicked.  Subsequent clicks will print to
stdout the time delta between the previous and current clicks.

The statusbar at the bottom shows: current timestamp, closest event
summary, timerange visible (both in ms and timestamps).  All
real-world time units rely on a valid SysInfo/CpuSpeed event in the
.vis file header, and it is printed to stdout on startup so check it
looks sane.

Right-click on a timeline highlights it by drawing it in fat grey;
click again to un-highlight.

Left-click on PIDs or TIDs in the yellow legend area pops up a tooltip
describing the containing PID and associated image name (assuming SysInfo
events are available).

Mouse-wheel-roll-up zooms the timescale in (event get wider appart),
mouse-wheel-roll-down zooms the timescale out (events get closer
together)

The "Goto..." button pops up a modal dialog allowing you to search
forwards from the "current timestamp" for the next named event, or the
next event bound to a tid timeline.  It also allows you to jump to any
absolute timestamp (eg cut-n-pasted from a logfile).  It beeps and
prints a warning if a search fails; on success it scrolls the window
to put the found event or timestamp just visible at the left-hand-side
of the window.
