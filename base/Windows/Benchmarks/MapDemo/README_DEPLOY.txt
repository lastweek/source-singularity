====================================================================
INTRODUCTION

This directory contains a port of the MapPoint-based "In Search of Caffeine" demo that was put together to demonstrate Singularity's process-isolation mechanism, and specifically the idea of using that mechanism to achieve strong sandboxing of application extensions by only furnishing the extension process with selected channels to trusted proxy components.

The port in this directory uses the .NET platform and is designed for deployment on Windows under IIS6/ASP.NET. Because of the much richer programming environment available on Windows, the ported version is vastly simpler than the Singularity version.

The port exists to allow overhead comparisons between Singularity and Windows when hosting this type of web application.

====================================================================
CAVEATS

The instructions below describe how I was able to get the webapp running under IIS6 / ASP.NET. There may have been an easier way that I wasn't aware of / didn't discover. Most of the deployment complexity comes from setting up the webapp to run under its own user account. This may be avoidable by having the webapp be specifically aware of having to use the corpnet web proxies, but it seemed instructive to go through the exercise of setting up a dedicated account for use by IIS, since this would be a key step in individually locking-down this specific webapp's capabilities on the server machine.

I wasn't able to find good documentation on why the permission changes to the WINDOWS\TEMP directory is necessary to get IIS to use the dedicated user account properly. It is only my experience that without this change, IIS fails complaining that it cannot access the TEMP directory adequately.

Also, in order to be a good comparison to the strong isolation achievable under Singularity, several additional steps would have to be taken by the server administrator to lock down the webapp on Windows. These steps are not detailed here, since it is assumed that by running the webapp in a dedicated app pool, under its own user account, all relevant machinery will be accounted for when performance is measured.

====================================================================
DEPLOYMENT INSTRUCTIONS

Here is how to deploy the mappoint demo webapp under IIS6 / ASP.NET.

- Set up a machine with an OS capable of running IIS6. This includes but is not limited to the Server 2003 SKUs.

- Install IIS using Add/Remove Windows Components (IIS is not installed by default).


The demo webapp needs to communicate with the MapPoint staging servers situated on the Internet. This requires the ISA Firewall client to be installed to allow proper communication through the corpnet proxies:

- Install the ISA Firewall client from ProductsWeb. Currently, ProductsWeb seems to end up pointing you to \\products\public\products\Applications\Server\ISA Server 2004\Standard\FPC\Program Files\Microsoft ISA Server\Clients\setup.exe.


As a security measure, the ISA firewall client won't proxy traffic for code running as the built-in service accounts, including NETWORK SERVICE, which is what IIS uses. So the demo webapp needs to run under its own user account:

- Create a new user account to run the webapp as.

- Add the new user account to the IIS_WPG group, or IIS will fail to run its worker processes under its identity.

- Use secpol.msc to add the new account to the list of accounts that can "log in as a service" (this security policy is under "User Rights Assignment\Log on as a service", or IIS will fail to run its worker processes under its identity.


Security policy is applied at startup, so it's necessary to reboot your machine sometime after applying the security-policy change, or things won't work.

Running a webapp under a user's credentials requires non-default access to the WINDOWS\TEMP directory:

- Go to the WINDOWS\TEMP directory's security permissions, and add the new user account to the list of entities with specific permissions. Copy the settings for the NETWORK SERVICE account, which should already be specifically listed. The permissions for the new account, which should correspond to NETWORK SERVICE, are "List Folder / Read Data" and "Delete". Specific steps:

   - Right-click on the WINDOWS\TEMP directory
   - Choose the "Security" tab
   - Press the "Advanced" button
   - Press the "Add..." button
   - Type in the name of your new user account in the dialog that pops up
   - Check "List Folder / Read Data" and "Delete" in the permissions dialog that pops up
   - Hit OK to exit the nested dialogs

This should complete the setup of the new user account. Now, using the MMC snapin for IIS (access "Administrative Tools -> Internet Information Services (IIIS) Manager"):

- Create a new application pool by right-clicking "Application Pools" and choosing "New->Application Pool". Allow the default settings to be used.

- Change properties of the new application pool by right-clicking and choosing "Properties":
   - Under the 'Identity' tab, switch the application pool to run under the new user account.

- Create a new web site by right-clicking "Web Sites" and choosing "New->Web site"
   - When creating the web site, create a new directory to host it under the c:\InetPub\wwwroot directory.

- Change properties of the new web site by right-clicking and choosing "Properties":
   - Under the 'Home Directory' tab, switch the application pool that the web site uses to the one you created.
   - Also under the 'Home Directory' tab, switch the "Execute Permissions" to "Scripts and Executables".

- Run nmake in this directory in the Singularity source tree. This should build a "distro" directory.

- Copy the entire "distro" tree into the directory you created to house the new web site under IIS. Do not copy the "distro" directory itself; that is, the top-level contents of the "distro" directory should become the top-level contents of the web site's directory.

- Point a web browser at the root URL for the web site you created. You should load the index.htm file and be able to walk through the demo.