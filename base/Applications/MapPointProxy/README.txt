MapPoint (aka Caffeinate Me!) Demo instructions

OK here's a reprise of the demo instructions to make sure they're up-to-date:

edit Distro\Scripts\MapDemo.script with an update to your proxy IP address (or delete that part if you have none)
msb Distro\World.proj
if the ISO (something like ...\base.obj\Distros\BVT.Debug.ApicMP.MarkSweep.Min.Concurrent.iso)
is NOT too big for your device (or you're using VPC) go to "Singularity machine setup"

if the ISO was too big or you're trying to maintain a small footprint:
Build steps
- msb Distro\BVT.proj (again)
- msb Applications\Network\NetworkApps.proj
- msb Applications\WebApps\WebApps.proj
- msb Applications\Cassini\Cassini.csproj [after building Applications\Webapps]
- msb Applications\MapPointProxy\MapPointProxy.csproj
- msb Applications\SeattleTrafficProxy\SeattleTrafficProxy.csproj
- msb Distro\BVT.proj (again)

Singularity machine setup:
- Be connected to the Internet.
- Boot the ISO on a device or mount the ISO image in the VPC cd-rom drive
  (something like ...\base.obj\Distros\BVT.Debug.ApicMP.MarkSweep.Min.Concurrent.iso)

Singularity runtime steps:
  (type at the shell as shown)
- Singularity> MapDemo (runs MapDemo.script)
  note Singularity's IP address

Client-side steps:

- Open IE
- Make sure IE is configured correctly to reach the Internet;
  the VE demos rely on IE being able to fetch image segments from the
  Internet.
- Make sure IE is configured correctly to retrieve local content directly
  from the Singularity box.
- Go to http://SingularitysIPAddressHere/

Other notes:
- On some laptops with wireless, it works to boot with PXE assigned to the
  wireless interface. This may have to do with MAC address spoofing being
  unsupported over wireless. Use the wired connection instead.

Disclaimers:
- Responses from the MapPoint staging servers are sometimes up to 15 seconds
  or so in arriving. Obviously, this is unrelated to Singularity performance.
  This manifests as a very noticeable delay in rendering the coffee-demo maps.
- I've seen the demos fall over in GC stack walks and in the memory allocator,
  suggesting we still have heap-corruption issues. For best results, bring up
  the Singularity machine fresh and present the demo right away to minimize
  heap pressure.
- A good strategy is to start the VPC, then pause it (from the menu or by
  typing right-alt-P), then resume it as you're ready to show the demo (from
  the menu or by typing right-alt-P).
