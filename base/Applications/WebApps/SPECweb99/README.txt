Here is how to run SPECweb:

Build:
- Applications\Wafgen99
- Applications\Network
- Applications\WebApps
- Applications\Cassini
- Distro

On Windows:
Run SPECweb99.exe. Install as "prime client"
Copy the rc.sing file into "c:\SPECweb99"
Edit the attached file to point to your Singularity machine
(you will need to get a DHCP lease as described below, first.
The DHCP server should give you the same address on subsequent runs)
Run "c:\SPECweb99\client -Z"
Separately:
- "cd c:\SPECweb99"
- "shrc"
- "specperl manager rc.sing"


On Singularity:

First run:
- "mkfs /dev/vol0.2"
- "fsmount /dev/vol0.2 /fs -n"
- "wafgen99 -v 10 /fs" [Generates lots of files]
- "fsunmount"
- reboot to clear the log

Notes:
- Use /dev/diskN instead of /dev/vol0.N if you want to use an unpartitioned disk.
- If want to support a maximum of 50 clients, use -v 50 instead of -v 10.

Subsequently:
- "fsmount /dev/vol0.2 /fs" [can take a while]
- "ipconfig /dev/nic0 dhcp start"
- "Cassini /app:SPECWeb99WebApp.x86 &"
or
- "Cassinin /app:SPECWeb99WebApp.x86 &"

