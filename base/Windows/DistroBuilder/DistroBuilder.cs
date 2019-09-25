////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DistroBuilder.cs
//
//  Note:   Main entry point for DistroBuilder tool, used to collect
//          application metadata into a manifest.
//
using System;
using System.IO;
using System.Xml;
using System.Diagnostics;
using System.Collections.Generic;
using System.Security.Cryptography;

public class DistroBuilder
{
    //
    // Fields in the distro build class
    //

    XmlNode systemPolicy; // the external xml policy

    // manifest and well-defined nodes
    XmlDocument systemManifest;
    XmlNode manifestRoot;
    XmlNode drivers;

    // internal node that we build and add to the manifest
    XmlNode fileList;

    // all files in the distro (full names, plus the separate directory prefix)
    string distroDirectoryName;
    readonly Set<String> applicationFiles = new Set<String>();
    readonly Set<String> manifestFiles = new Set<String>();
    readonly Set<String> otherFiles = new Set<String>();

    // key filenames
    string kernelPath;      // kernel path+name
    string systemPath;      // system manifest path+name
    string systemName;      // just the name of the manifest
    string iniFilePath;     // ini file

    // whether this is a subordinate kernel or not
    bool subordinateKernel;

    static string[] nativeSuffixes = { ".x86", ".x64", ".arm" };

    private static bool IsNativeBinaryName(string path)
    {
        foreach (string suffix in nativeSuffixes) {
            if (path.EndsWith(suffix)) {
                return true;
            }
        }
        return false;
    }

    private static bool IsManifestName(string path)
    {
        return (path.EndsWith(".manifest"));
    }

    private static string NativeBinaryToPrefix(string path)
    {
        foreach (string suffix in nativeSuffixes) {
            if (path.EndsWith(suffix)) {
                return path.Substring(0, path.Length - suffix.Length);
            }
        }
        return null;
    }

    private static string NativeBinaryToManifest(string path)
    {
        string prefix = NativeBinaryToPrefix(path);
        if (prefix != null) {
            return prefix + ".manifest";
        }
        return null;
    }

    private static string StripPathFromFile(string path)
    {
        int index = path.LastIndexOf('/');
        if (index < 0) {
            index = path.LastIndexOf('\\');
        }
        if (index >= 0) {
            return path.Substring(index + 1);
        }
        return path;
    }

    // set up an object that can build the distribution
    internal DistroBuilder(string kernelFile,
                           string policyFile,
                           string outputFile,
                           string iniFile,
                           string distroDirectoryName,
                           string distroDescriptionFileName,
                           bool subKernel)
    {
        subordinateKernel = subKernel;

        kernelPath = kernelFile;

        // copy output file names.
        systemPath = outputFile;
        iniFilePath = iniFile;

        // load the system policy.
        XmlDocument policyDoc = new XmlDocument();
        policyDoc.Load(policyFile);
        systemPolicy = GetChild(policyDoc, "distribution");

        // set up Xml pieces.
        systemManifest = new XmlDocument();
        manifestRoot = systemManifest.CreateElement("system");
        systemManifest.AppendChild(manifestRoot);

        fileList = AddElement(null, "files");
        drivers = AddElement(null, "drivers");

        FileInfo allFiles = new FileInfo(distroDescriptionFileName);
        StreamReader stream = allFiles.OpenText();

        for (string s = null; (s = stream.ReadLine()) != null;) {
            if (IsNativeBinaryName(s)) {
                if (s.Equals(kernelPath, StringComparison.OrdinalIgnoreCase)) {
                    // The kernel doesn't go in the default binary list.
                    continue;
                }
                applicationFiles.Add(s);
            }
            else if (IsManifestName(s)) {
                manifestFiles.Add(s);
            }
            else {
                otherFiles.Add(s);
            }
        }
        stream.Close();

        // add the output file to the list
        systemName = StripPathFromFile(systemPath);

        FileInfo outFile = new FileInfo(systemPath);
        systemPath = outFile.FullName;
        if (!otherFiles.ContainsKey(systemPath)) {
            otherFiles.Add(systemPath);
        }

        // now get the fully path for the distro directory name
        FileInfo directoryInfo = new FileInfo(distroDirectoryName);
        this.distroDirectoryName = directoryInfo.FullName;
    }

    const string ServiceConfigElementName = "serviceConfig";
    const string ServiceElementName = "service";
    const string ServiceNameAttributeName = "name";
    const string ManifestNameAttributeName = "binary";
    const string ServiceActivationModeAttributeName = "activationMode";

    /// <summary>
    /// This method modifies the system manifest XML document by inserting service elements for
    /// services specified on the command line.  If any existing service elements are found that
    /// have the same service name, then the service specification provided on the command line
    /// overrides the existing service specification.
    /// </summary>
    /// <param name="document">The policy document to modify.</param>
    /// <param name="services">The set of service specifications to add to the document.</param>
    internal void AddServicesToSystemManifest(XmlElement serviceConfigElement, IEnumerable<ServiceInfo> services)
    {
        XmlDocument document = serviceConfigElement.OwnerDocument;
        Dictionary<String, XmlElement> existingServices = new Dictionary<String, XmlElement>();

        // First, build an index of all of the existing <service> elements,
        // using the value of the 'name' attribute as the key.
        foreach (XmlNode node in serviceConfigElement.ChildNodes) {
            if (node.NodeType != XmlNodeType.Element) {
                continue;
            }

            XmlElement element = (XmlElement)node;
            if (element.Name != ServiceElementName) {
                continue;
            }

            string serviceName = element.GetAttribute(ServiceNameAttributeName);
            if (String.IsNullOrEmpty(serviceName)) {
                continue;
            }

            existingServices[serviceName] = element;
        }

        foreach (ServiceInfo service in services) {
            string serviceName = service.ServiceName;
            XmlElement serviceElement;
            if (existingServices.TryGetValue(serviceName, out serviceElement)) {
                WriteWarningLine("Found existing service '{0}' in source policy document.  Overriding with values specified on command line.", serviceName);
            }
            else {
                serviceElement = document.CreateElement(ServiceElementName);
                serviceConfigElement.AppendChild(serviceElement);
                serviceElement.SetAttribute(ServiceNameAttributeName, serviceName);
                existingServices.Add(serviceName, serviceElement);
            }

            serviceElement.SetAttribute(ServiceActivationModeAttributeName, service.ActivationMode);
            serviceElement.SetAttribute(ManifestNameAttributeName, service.ManifestName);
        }
    }

    //////////////////////////////////////////////// Methods to help with XML.
    //
    private XmlElement AddElement(XmlElement parent, string name)
    {
        XmlElement element = systemManifest.CreateElement(name);
        if (parent != null) {
            parent.AppendChild(element);
        }
        return element;
    }

    private XmlNode AddImported(XmlNode parent, XmlNode root, bool deep)
    {
        XmlNode element = systemManifest.ImportNode(root, true);
        if (parent != null) {
            parent.AppendChild(element);
        }
        return element;
    }

    // Return an array with every child of the parent whose name matches
    // <name>
    private static XmlNode[] GetChildren(XmlNode parent, string name)
    {
        List<XmlNode> result = new List<XmlNode>();

        foreach (XmlNode child in parent.ChildNodes) {
            if (child.Name == name) {
                result.Add(child);
            }
        }

        if (result.Count == 0) {
            return new XmlNode[0];
        }

        XmlNode[] children = new XmlNode [result.Count];
        for (int i = 0; i < result.Count; i++) {
            children[i] = (XmlNode)result[i];
        }
        return children;
    }

    // Get the first child named `name'
    private static XmlNode GetChild(XmlNode parent, string name)
    {
        return parent[name];
    }

    // Get end node along a path of first matches
    private static XmlNode GetDescendant(XmlNode root, string [] path)
    {
        XmlNode parent = root;

        foreach (string pathelement in path) {
            parent = GetChild(parent, pathelement);
            if (parent == null) {
                return null;
            }
        }
        return parent;
    }

    // Get the named attribute if it exists.
    private static string GetAttribute(XmlNode node, string attrib)
    {
        XmlAttribute xa = node.Attributes[attrib];
        return xa != null ? xa.Value : null;
    }

    private static string GetAttribute(XmlNode node, string attrib, string value)
    {
        XmlAttribute xa = node.Attributes[attrib];
        return xa != null ? xa.Value : value;
    }

    private static int GetAttribute(XmlNode node, string attrib, int value)
    {
        XmlAttribute xa = node.Attributes[attrib];
        return xa != null ? Int32.Parse(xa.Value) : value;
    }

    //////////////////////////////////////////////////////////////////////////

    // return true if the node's name is in names.
    private bool TestNodeIs(XmlNode node, string [] names)
    {
        foreach (string name in names) {
            if (node.Name == name) {
                return true;
            }
        }
        return false;
    }

    const string DriverElementName = "driver";

    // TODO: this attribute create code should be in a function!
    // add a DriverCategory node into the <drivers>
    private void AddDriverNode(string name, string path,
                               string signature, string iclass,
                               IEnumerable<XmlNode> values)
    {
        // create the new node
        XmlElement driver = systemManifest.CreateElement(DriverElementName);

        // set its name, signature, and path
        driver.SetAttribute("name", name);
        driver.SetAttribute("signature", signature);
        driver.SetAttribute("path", path);
        if (iclass != "") {
            driver.SetAttribute("class", iclass);
        }

        // add any enumerates via copy.
        foreach (XmlNode node in values) {
            driver.AppendChild(node.CloneNode(true));
        }

        // and insert this node into the registry:
        drivers.AppendChild(driver);
    }

    // given a driverCategory that potentially has many device signatures, split
    // it by device and create an entry in the drivers for each device
    private void CreateRegistryEntriesFromCategory(XmlNode category,
                                                   string name,
                                                   string path)
    {
        List<XmlNode> values = new List<XmlNode>();

        // first parse the entries in the driver category to fill out the
        // Endpoint, FixedHardware, and DynamicHardware sets
        string iclass = GetAttribute(category, "class", "");

        // now populate these with children based on a few basic matching rules
        foreach (XmlNode node in category.ChildNodes) {
            if (node.Name == "enumerates" ||
                node.Name == "endpoints" ||
                node.Name == "fixedHardware" ||
                node.Name == "dynamicHardware" ||
                node.Name == "configs") {
                values.Add(AddImported(null, node, true));
            }
            else if (node.Name != "device") {
                //
            }
        }

        // get every device signature in this driver category
        XmlNode[] signatureTags = GetChildren(category, "device");

        // there's a chance (for example, with the Hal) that there are no
        // signatures.  In this case, we process the category once, with a null
        // signature
        if (signatureTags.Length == 0) {
            AddDriverNode(name, path, "", iclass, values);
        }
        else {
            foreach (XmlNode signature in signatureTags) {
                string value = GetAttribute(signature, "signature", "");
                AddDriverNode(name, path, value, iclass, values);
            }
        }
    }

    // This is the main method for creating a driver registry.
    public void CreateDriverRegistry()
    {
        foreach (string filename in manifestFiles) {
            // get the manifest as an Xml document
            XmlDocument manifestDoc = new XmlDocument();
            manifestDoc.Load(filename);

            XmlNode application = GetChild(manifestDoc, "application");

            // Read the name and path from the manifest
            string name = GetAttribute(application, "name");

            // Console.WriteLine("{0}:", filename);
            foreach (XmlNode process in GetChildren(application, "process")) {
                string path = GetAttribute(process, "path", "");

                foreach (XmlNode categories in GetChildren(process, "categories")) {
                    foreach (XmlNode category in GetChildren(categories, "category")) {
                        if (GetAttribute(category, "name") != "driver") {
                            continue;
                        }

                        string iclass = GetAttribute(category, "class", "");

                        // now process all DriverCategories
                        CreateRegistryEntriesFromCategory(category, name, path);
                    }
                }
            }
        }
    }

    private bool NamesMatch(string target, string prefix, bool isPrefix)
    {
        int len = isPrefix ? prefix.Length :
            (target.Length > prefix.Length ? target.Length : prefix.Length);

        return (String.Compare(target, 0, prefix, 0, len, true) == 0);
    }


    // Remove unwanted drivers from the rot using the policy.
    private void RemoveNodes(XmlNode root, XmlNode policy)
    {
        foreach (XmlNode rule in policy.ChildNodes) {
            string attrName = "";
            string attrVal = "";
            bool isPrefix = false;

            if (rule.Name == "driver") {
                attrName = "name";
            }
            else if (rule.Name == "device") {
                attrName = "signature";
                isPrefix = true;
            }
            else {
                continue;
            }
            List<XmlNode> removals = new List<XmlNode>();
            attrVal = GetAttribute(rule, attrName);
            foreach (XmlNode candidate in root.ChildNodes) {
                string target = GetAttribute(candidate, attrName);

                if (NamesMatch(target, attrVal, isPrefix)) {
                    removals.Add(candidate);
                }
            }
            foreach (XmlNode oldnode in removals) {
                root.RemoveChild(oldnode);
            }
        }
    }

    // in addition, we use the imperative mechanism to create the "follows"
    // ordering, which lets us specify a more total order on the initialization
    // of drivers
    private void ApplyOrdering(XmlNode root, XmlNode policy)
    {
        foreach (XmlNode rule in policy.ChildNodes) {
            string signature = GetAttribute(rule, "signature");
            string name = GetAttribute(rule, "name");
            foreach (XmlNode candidate in root.ChildNodes) {
                if (candidate.NodeType != XmlNodeType.Element)
                    continue;

                string candidatesignature = GetAttribute(candidate, "signature");
                if (candidatesignature.StartsWith(signature)) {
                    XmlElement tag = AddElement((XmlElement)candidate, rule.Name);
                    tag.SetAttribute("name", name);
                }
            }
        }
    }

    // and this is the master method for applying the imperative policy
    private void ApplyPolicyToRegistry()
    {
        // get its driversConfig:
        XmlNode policy = GetChild(systemPolicy, "driverRegistryConfig");

        // go through each imperative command
        foreach (XmlNode child in policy.ChildNodes) {
            if (child.Name == "remove") {
                RemoveNodes(drivers, child);
            }
            else if (child.Name == "ordering") {
                ApplyOrdering(drivers, child);
            }
        }
    }

    // This prints the distribution manifest when all is done
    public void PrintManifestFile()
    {
        XmlTextWriter w = new XmlTextWriter(systemPath,
                                            System.Text.Encoding.UTF8);
        w.Formatting = Formatting.Indented;
        systemManifest.Save(w);
        w.Close();
    }

    // TODO: there ought to be some policy that decides what should
    //       to in the distribution, but for now we just take as
    //       input a list of files that have been built, and assume
    //       it is the output of this alluded-to step

    // Every file in the distro must be added to a list, both so that the file
    // can be added to SingBoot.ini, and so that it can have a filename
    // associated with it in the namespace
    private void AddFileNode(string pathName, int index, bool visible,
                             int manifestIndex)
    {
        XmlElement file = AddElement(null, "file");

        // get values for all the attributes of this file:
        bool isExecutable = (IsNativeBinaryName(pathName) &&
                             !pathName.Equals(kernelPath, StringComparison.OrdinalIgnoreCase));
        bool isManifest = IsManifestName(pathName);
        string shortName = StripPathFromFile(pathName).ToLower();

        string [] nameSet = pathName.Split('\\');
        int fileIndex = 0;
        for (int i = 0; i < nameSet.Length; i++) {
            if (nameSet[i] == "Files") {
                fileIndex = i;
                break;
            }
        }
        // if this is the "/Distro/Files" directory
        // allow subdirectories in the short name
        if (fileIndex > 0 && (((nameSet.Length - 1) - fileIndex > 1))) {
            isExecutable = false;
            isManifest = false;
            shortName = null;
            for (int i = fileIndex + 1; i < nameSet.Length; i++) {
                shortName = shortName + "/" + nameSet[i].ToLower();
            }
        }
        string distroName = pathName.Remove(0, distroDirectoryName.Length);
        distroName = distroName.Replace('\\', '/');

        // add the attributes:
        file.SetAttribute("distroName", distroName);
        file.SetAttribute("name", shortName);
        file.SetAttribute("id", index.ToString());

        if (isExecutable) {
            file.SetAttribute("executable", "true");
        }
        else if (isManifest) {
            file.SetAttribute("manifest", "true");
        }

        if (manifestIndex > 0) {
            file.SetAttribute("manifestId", manifestIndex.ToString());
        }

        // add the file to the master file list
        fileList.AppendChild(file);
    }

    // This calls the above method to populate the fileList with all files that
    // are to be included in the distribution
    private void BuildFileList()
    {
        int position = 3;

        // first of all, let's set the kernel.dmp and output manifest file
        // entries
        AddFileNode(kernelPath, 0, false, 2);
        AddFileNode(systemPath, 1, false, -1);
        AddFileNode(NativeBinaryToManifest(kernelPath), 2, false, -1);

        if (!subordinateKernel) {

            // now let's build the file list:
            // get the policy on what goes in the bootscript
            XmlNode policy = GetDescendant(systemPolicy, new string[] {"bootScript",
                                                                       "folders"});
            foreach (XmlNode rule in policy.ChildNodes) {
                if (rule.Name != "folder") {
                    continue;
                }
                string folder = GetAttribute(rule, "name");
                foreach (string applicationName in applicationFiles) {
                    string manifestName = applicationName + ".manifest";
                    string shortAppName = applicationName.Replace(distroDirectoryName, "");
                    if (shortAppName.StartsWith("\\" + folder)) {
                        if (manifestFiles.ContainsKey(manifestName)) {
                            AddFileNode(applicationName, position, true,
                                        ++position);
                            AddFileNode(manifestName, position, true, -1);
                        }
                        else {
                            AddFileNode(applicationName, position, true, -1);
                        }
                        position++;
                    }
                }
                foreach (string fileName in otherFiles) {
                    string shortFileName = fileName.Replace(distroDirectoryName, "");
                    if (shortFileName.StartsWith("\\" + folder)) {
                        AddFileNode(fileName, position++, true, -1);
                    }
                }
                // NB - we don't copy a manifest unless we've associated it with an
                // app
            }
        }
    }

    // Given only a list of drivers, a list of files, and some policy, we need
    // to create a system manifest.  This is how we do it for now.
    internal void InstallPolicies(IEnumerable<ServiceInfo> services)
    {
        // build the file list that goes into the manifest
        BuildFileList();

        // set up the initConfig tag and append the file list to it
        XmlNode initConfig = GetChild(systemPolicy, "initConfig");
        XmlNode newInitConfig = systemManifest.ImportNode(initConfig, true);
        newInitConfig.AppendChild(fileList);

        // get the namingConventions
        XmlNode namingConventions = GetChild(systemPolicy, "namingConventions");
        XmlNode newNaming = systemManifest.ImportNode(namingConventions, true);

        // get process grouping data
        XmlNode processConfig = GetChild(systemPolicy, "processConfig");
        XmlNode newProcessConfig = null;
        if (processConfig != null) {
            newProcessConfig = systemManifest.ImportNode(processConfig, true);
        }

        // get service configurations
        XmlNode serviceConfig = GetChild(systemPolicy, ServiceConfigElementName);
        XmlElement newServiceConfig = serviceConfig != null ? (XmlElement)systemManifest.ImportNode(serviceConfig, true)
            : systemManifest.CreateElement(ServiceConfigElementName);
        AddServicesToSystemManifest(newServiceConfig, services);


        // apply the imperative policy to the Driver Registry (this prunes it)
        ApplyPolicyToRegistry();

        // add everything to the manifest
        manifestRoot.AppendChild(drivers);
        manifestRoot.AppendChild(newNaming);
        manifestRoot.AppendChild(newServiceConfig);
        if (newProcessConfig != null) {
            manifestRoot.AppendChild(newProcessConfig);
        }
        manifestRoot.AppendChild(newInitConfig);
    }

    // When everything is set, we still need the Singboot.ini
    // file.  This is how we make it:
    public void MakeIniFile(string distrodir)
    {
        using (StreamWriter stream = new StreamWriter(iniFilePath, false)) {
            string ruler = new String('#', 79);
            stream.WriteLine(ruler);
            stream.WriteLine("# SingBoot.ini");
            stream.WriteLine("# Build Date: {0}", System.DateTime.Now.ToString());
            stream.WriteLine(ruler);

            using (MD5 md5 = MD5.Create()) {
                foreach (XmlNode file in fileList) {
                    string installedFileName = GetAttribute(file, "distroName");
                    string originalFileName =
                        distrodir + installedFileName.Replace("/", "\\");

                    FileInfo fileInfo = new FileInfo(originalFileName);
                    using (FileStream fs = fileInfo.OpenRead()) {
                        byte[] hash = md5.ComputeHash(fs);
                        stream.Write("Hash-MD5=");
                        foreach (byte b in hash) {
                            stream.Write("{0:x2}", b);
                        }
                    }

                    stream.WriteLine(" Size={0} Path={1}",
                                     fileInfo.Length, installedFileName);
                }
            }
            // NB Trailing ruler helps identify the end of file
            stream.WriteLine(ruler);
        }
    }

    /// <summary>
    /// Writes an error line that matches the Visual Studio format for errors.
    /// This allows VS to find the errors in its output window.
    /// </summary>
    /// <param name="line">The error message to write.</param>
    static void WriteErrorLine(string message)
    {
        Console.WriteLine("error : " + message);
    }

    static void WriteErrorLine(string format, params object[] args)
    {
        WriteErrorLine(String.Format(format, args));
    }

    static void WriteWarningLine(string message)
    {
        Console.WriteLine("warning : " + message);
    }

    static void WriteWarningLine(string format, params object[] args)
    {
        WriteErrorLine(String.Format(format, args));
    }

    // Print the correct command line args for the program
    static void PrintUsage()
    {
        Console.WriteLine(
            "Usage:\n" +
            "    distrobuilder [options]\n" +
            "Options:\n" +
            "    /desc:<desc>        - Distribution description.\n" +
            "    /dir:<path>         - Set distribution root directory\n" +
            "    /ini:<ini>          - Set output boot.ini file.\n" +
            "    /kernel:<kernel>    - Set input kernel file.\n" +
            "    /out:<file>         - Set name of output system manifest.\n" +
            "    /policy:<file>      - Set input system policy file.\n" +
            "Summary:\n" +
            "    Builds a system manifest for a collection of application manifests and\n" +
            "    a file list.\n" +
            "");
    }

    // main entry point:
    static int Main(string[] args)
    {
        string outfile = null;
        string policyfile = null;
        string distrodir = null;
        string distrodesc = null;
        string inifile = null;
        string kernelfile = null;

        bool errors = false;

        bool subKernel = false;

        List<ServiceInfo> services = new List<ServiceInfo>();

        // parse the cmdline
        foreach (string arg in args) {
            if (arg.StartsWith("/") || arg.StartsWith("-")) {
                int separator = arg.IndexOf(':', 1);
                if (separator == -1) {
                    separator = arg.IndexOf('=', 1);
                }

                string name;
                string value;

                if (separator != -1) {
                    name = arg.Substring(1, separator - 1);
                    value = arg.Substring(separator + 1);
                }
                else {
                    name = arg.Substring(1);
                    value = "";
                }

                name = name.ToLower();

                switch (name) {
                    case "desc":
                        if (value == "") {
                            WriteErrorLine("The '/desc' argument requires a value.");
                            errors = true;
                            break;
                        }
                        distrodesc = value;
                        break;

                    case "dir":
                        if (value == "") {
                            WriteErrorLine("The '/dir' argument requires a value.");
                            errors = true;
                            break;
                        }
                        distrodir = value;
                        break;

                    case "ini":
                        if (value == "") {
                            WriteErrorLine("The '/ini' argument requires a value.");
                            errors = true;
                            break;
                        }
                        inifile = value;
                        break;

                    case "kernel":
                        if (value == "") {
                            WriteErrorLine("The '/kernel' argument requires a value.");
                            errors = true;
                            break;
                        }
                        kernelfile = value;
                        break;

                    case "out":
                        if (value == "") {
                            WriteErrorLine("The '/out' argument requires a value.");
                            errors = true;
                            break;
                        }
                        outfile = value;
                        break;

                    case "policy":
                        if (value == "") {
                            WriteErrorLine("The '/policy' argument requires a value.");
                            errors = true;
                            break;
                        }
                        policyfile = value;
                        break;

                    case "service": {
                        if (value == "") {
                            WriteErrorLine("The '/service' argument requires a value.");
                            errors = true;
                            break;
                        }
                        ServiceInfo service;
                        try {
                            service = ParseServiceSpecification(value);
                        }
                        catch (ParseException ex) {
                            WriteErrorLine("The service description provided to the '/service' switch is invalid.");
                            WriteErrorLine("The value is: " + value);
                            WriteErrorLine(ex.Message);
                            errors = true;
                            break;
                        }

                        Debug.Assert(service != null);

                        bool foundExisting = false;
                        foreach (ServiceInfo existingService in services) {
                            if (existingService.ServiceName == service.ServiceName) {
                                foundExisting = true;
                                break;
                            }
                        }

                        if (foundExisting) {
                            WriteErrorLine("The service '{0}' is specified more than once on the command line.");
                            errors = true;
                        }
                        else {
                            services.Add(service);
                        }
                        break;
                    }


                    case "subordinate":
                        subKernel = true;
                        break;

                    case "help":
                    case "?":
                        PrintUsage();
                        return 0;

                    default:
                        WriteErrorLine("The '/{0}' argument is not recognized.", arg);
                        errors = true;
                        break;
                }
            }
            else {
                WriteErrorLine("Unrecognized argument: " + arg);
                errors = true;
            }
        }

        if (String.IsNullOrEmpty(kernelfile)) {
            WriteErrorLine("The '/kernel' argument is required, but is not provided.");
            errors = true;
        }

        if (String.IsNullOrEmpty(policyfile)) {
            WriteErrorLine("The '/policy' argument is required, but is not provided.");
            errors = true;
        }

        if (String.IsNullOrEmpty(outfile)) {
            WriteErrorLine("The '/out' argument is required, but is not provided.");
            errors = true;
        }

        if (String.IsNullOrEmpty(distrodesc)) {
            WriteErrorLine("The '/desc' argument is required, but is not provided.");
            errors = true;
        }

        if (String.IsNullOrEmpty(distrodir)) {
            WriteErrorLine("The '/dir' argument is required, but is not provided.");
            errors = true;
        }

        if (String.IsNullOrEmpty(inifile)) {
            WriteErrorLine("The '/ini' argument is required, but is not provided.");
            errors = true;
        }

        if (errors) {
            return 1;
        }

        // check all input files
        if (!File.Exists(kernelfile)) {
            WriteErrorLine("Error: kernel file '{0}' not found", kernelfile);
            errors = true;
        }
        if (!File.Exists(policyfile)) {
            WriteErrorLine("Error: policy file '{0}' not found", policyfile);
            errors = true;
        }
        if (!File.Exists(distrodesc)) {
            WriteErrorLine("Error: distro desc file '{0}' not found", distrodesc);
            errors = true;
        }
        if (!Directory.Exists(distrodir)) {
            WriteErrorLine("Error: directory '{0}' not found", distrodir);
            errors = true;
        }

        if (errors) {
            return 1;
        }

#if false
        try {
#endif
            DistroBuilder p = new DistroBuilder(
                kernelfile, policyfile, outfile, inifile, distrodir, distrodesc, subKernel);

            // first aggregate all drivers into a <DriverRegistry>
            p.CreateDriverRegistry();
            // now apply policy to the system config
            p.InstallPolicies(services);
            // then output the manifest
            p.PrintManifestFile();
            // lastly make the ini file
            p.MakeIniFile(distrodir);
            return 0;
#if false
        }
        catch (Exception ex) {
            for (Exception current = ex; current != null; current = current.InnerException) {
                WriteErrorLine(current.Message);
            }
            return 1;
        }
#endif
    }

    /// <summary>
    /// This method parses the service specifications passed on the command line
    /// with the '/service:' switch.
    /// </summary>
    /// <remarks>
    /// The specification has the format:
    ///
    ///     name(,arg=value)*
    ///
    /// where the valid arguments are:
    ///     * manifest: Specifies the manifest name (binary name) for this service.
    ///         The default is the same as the service name.
    ///     * type: Specifies the service type, one of "managed" or "unmanaged".
    ///         The default is "managed".
    /// </remarks>
    /// <param name="arg">The specification.</param>
    /// <returns></returns>
    /// <exception cref="ParseException">Thrown if the specification is not valid.</exception>
    static ServiceInfo ParseServiceSpecification(string spec)
    {
        char[] word_splitters = { ',', ';' };
        string[] words = spec.Split(word_splitters);
        Debug.Assert(words != null);

        if (words.Length == 0) {
            throw new ParseException("No values provided in service specification.");
        }

        string serviceName = words[0];

        if (String.IsNullOrEmpty(serviceName)) {
            throw new ParseException("The service name is invalid.");
        }

        string manifestName = null;
        string activationMode = null;

        for (int i = 1; i < words.Length; i++) {
            string word = words[i];
            int equals_index = word.IndexOf('=');
            if (equals_index == -1) {
                equals_index = word.IndexOf(':');
            }
            if (equals_index == -1) {
                throw new ParseException(String.Format("The value '{0}' does not have a value separator ('=' or ':').", word));
            }

            string name = word.Substring(0, equals_index);
            string value = word.Substring(equals_index + 1);

            name = name.ToLower();

            switch (name) {
                case "manifest":
                    // Ignore entries with empty value.
                    if (String.IsNullOrEmpty(value)) {
                        break;
                    }
                    // Duplicate 'manifest' values are illegal.
                    if (!String.IsNullOrEmpty(manifestName)) {
                        throw new ParseException("Duplicate 'manifest' values are illegal.");
                    }
                    manifestName = value;
                    break;

                case "mode":
                    if (String.IsNullOrEmpty(value)) {
                        throw new ParseException("The 'mode' value for the /service switch requires a value, but none was provided.");
                    }

                    value = value.ToLower();
                    if (!IsValidServiceActivationMode(value)) {
                        throw new ParseException(String.Format("The value '{0}' is not a valid service activation mode.", value));
                    }

                    if (!String.IsNullOrEmpty(activationMode)) {
                        throw new ParseException("The service activation mode has already been specified.");
                    }

                    activationMode = value;
                    break;

                default:
                    throw new ParseException(String.Format("The service parameter '{0}' is not recognized.", name));
            }
        }

        if (String.IsNullOrEmpty(manifestName)) {
            manifestName = serviceName;
        }

        if (String.IsNullOrEmpty(activationMode)) {
            activationMode = "demand";
        }

        ServiceInfo service = new ServiceInfo();
        service.ServiceName = serviceName;
        service.ActivationMode = activationMode;
        service.ManifestName = manifestName;

        return service;
    }

    static bool IsValidServiceActivationMode(string mode)
    {
        return mode == "demand" || mode == "alwaysactive" || mode == "manual";
    }

}

internal class ServiceInfo
{
    public string ServiceName;
    public string ManifestName;

    /// <summary>
    /// One of "Demand", "AlwaysActive", or "Manual".
    /// </summary>
    public string ActivationMode;
}

class ParseException : Exception
{
    public ParseException(string msg)
        : base(msg)
    {
    }
}

class Set<T> : IEnumerable<T>
{
    SortedList<T,bool> _list = new SortedList<T,bool>();

    public IEnumerator<T> GetEnumerator()
    {
        return _list.Keys.GetEnumerator();
    }

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
    {
        return _list.Keys.GetEnumerator();
    }

    public void Add(T value)
    {
        _list.Add(value, true);
    }

    public bool ContainsKey(T value)
    {
        return _list.ContainsKey(value);
    }
}

