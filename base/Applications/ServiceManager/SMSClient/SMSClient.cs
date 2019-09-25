///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Service Manager client program
//
using System;
using System.Threading;

using Microsoft.SingSharp;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Contracts;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.ServiceManager;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications.ServiceManager
{
    [ConsoleCategory(HelpMessage="Service management client", DefaultAction=true)]
    internal class DefaultConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal DefaultConfig();

        internal int AppMain()
        {
            Console.WriteLine("Use -? for help.");
            return 0;
        }
    }

    [ConsoleCategory(Action="start", HelpMessage="Start a service")]
    internal class StartConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        // [BoolParameter("w", Mandatory=false, HelpMessage="Wait for service to start.")]
        public bool wait;

        reflective internal StartConfig();

        internal int AppMain()
        {
            return SMSClient.StartService((!)serviceName, wait);
        }
    }

    [ConsoleCategory(Action="stop", HelpMessage="Stop a service")]
    internal class StopServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        // [BoolParameter("w", Mandatory=false, HelpMessage="Wait for service to stop.")]
        public bool wait;

        reflective internal StopServiceCommand();

        internal int AppMain()
        {
            return SMSClient.StopService((!)serviceName, wait);
        }
    }

    [ConsoleCategory(Action="list", HelpMessage="Show a list of services")]
    internal class ListConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal ListConfig();

        internal int AppMain()
        {
            return SMSClient.ListServices(this);
        }
    }

    [ConsoleCategory(Action="show", HelpMessage="Show details about a specific service.")]
    internal class ShowServiceParameters
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Position=0, Mandatory=true, HelpMessage="The service to examine.")]
        public string ServiceName;

        reflective internal ShowServiceParameters();

        internal int AppMain()
        {
            if (ServiceName == null) {
                Console.WriteLine("The 'service' parameter is required, but has not been provided.");
                return -1;
            }

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {
                ServiceError error = SMSClient.SelectService(svmanager, this.ServiceName);
                if (error != ServiceError.None)
                    return -1;

                bool errors = false;

                svmanager.SendQueryServiceConfig();
                switch receive {
                    case svmanager.CurrentServiceConfig(config):
                        SMSClient.ShowConfigDetailed(config);
                        config.Dispose();
                        break;

                    case svmanager.RequestFailed(err):
                        if (err == ServiceError.ServiceNotFound) {
                            Console.WriteLine("There is no service with name '{0}'.", this.ServiceName);
                            return -1;
                        }

                        Console.WriteLine("Failed to query service configuration.");
                        SMSClient.ShowServiceError(err);
                        errors = true;
                        break;

                    case svmanager.ChannelClosed():
                        Console.WriteLine("The Service Manager closed its channel unexpectedly.");
                        return -1;
                }

                svmanager.SendQueryServiceStatus();
                switch receive {
                    case svmanager.CurrentServiceStatus(status):
                        Console.WriteLine();
                        SMSClient.ShowStatusDetailed(status);
                        status.Dispose();
                        break;

                    case svmanager.RequestFailed(err):
                        Console.WriteLine("Failed to query service status.");
                        SMSClient.ShowServiceError(err);
                        errors = true;
                        break;

                    case svmanager.ChannelClosed():
                        Console.WriteLine("The Service Manager closed its channel unexpectedly.");
                        return -1;
                }

                if (errors)
                    return -1;
                else
                    return 0;

            }
            finally {
                delete svmanager;
            }
        }
    }

    [ConsoleCategory(Action="watch", HelpMessage="Watch the status of a service")]
    internal class WatchConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        reflective internal WatchConfig();

        internal int AppMain()
        {
            return SMSClient.WatchService((!)serviceName);
        }
    }

    [ConsoleCategory(Action="watchall", HelpMessage="Watch the status of the Service Manager")]
    internal class WatchAllConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

#if false
        [BoolParameter("c", Mandatory=false, HelpMessage="Watch all service configuration changes")]
        public bool watchConfigChanges;

        [BoolParameter("s", Mandatory=false, HelpMessage="Watch all service status changes")]
        public bool watchStatusChanges;
#endif

        reflective internal WatchAllConfig();

        internal int AppMain()
        {
#if false
            ServiceManagerEventMask desiredEvents = 0;

            if (watchConfigChanges)
                desiredEvents |= ServiceManagerEventMask.AnyServiceConfig;

            if (watchStatusChanges)
                desiredEvents |= ServiceManagerEventMask.AnyServiceStatus;

            if (desiredEvents == 0)
                desiredEvents = ServiceManagerEventMask.AnyServiceConfig | ServiceManagerEventMask.AnyServiceStatus;
#else
            ServiceManagerEventMask desiredEvents = ServiceManagerEventMask.AnyServiceConfig | ServiceManagerEventMask.AnyServiceStatus;
#endif

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();

            svmanager.SendWatchServiceManager(desiredEvents);

            switch receive {
                case svmanager.Ok():
                    break;

                case svmanager.RequestFailed(error):
                    Console.WriteLine("The Service Manager rejected the subscription request.");
                    SMSClient.ShowServiceError(error);
                    delete svmanager;
                    return -1;
            }

            Console.WriteLine("Watching Service Manager...");

            for (;;) {
                Console.WriteLine("Sending WaitNextServiceManagerChange");
                svmanager.SendWaitNextServiceManagerChange();

                Console.WriteLine("switch-receive");

                switch receive {
                    case svmanager.ServiceManagerChanged(events):
                        Console.WriteLine("Service Manager events fired: {0:x8}", ((uint)events));
                        break;
                }
            }
        }
    }

    [ConsoleCategory(Action="create", HelpMessage="Create a new service entry")]
    internal class CreateServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        [StringParameter("exe", Mandatory=false, HelpMessage="Executable to use; if omitted, uses service name.")]
        public string executableName;

        [StringParameter("display", Mandatory=false, HelpMessage="Display name to use; if omitted, uses service name.")]
        public string displayName;

        [BoolParameter("disabled", Mandatory=false, HelpMessage="Create in a disabled state.")]
        public bool isAdministrativelyDisabled;

        reflective internal CreateServiceCommand();

        internal int AppMain()
        {
            assert serviceName != null;
            if (serviceName.Length == 0) {
                Console.WriteLine("Invalid service name.");
                return -1;
            }

            if (executableName == null || executableName.Length == 0)
                executableName = serviceName;

            if (displayName == null || displayName.Length == 0)
                displayName = serviceName;

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {

                ServiceConfig config = new ServiceConfig();
                config.ServiceName = Bitter.FromString2(serviceName);
                config.ExecutableName = Bitter.FromString2(executableName);
                config.DisplayName = Bitter.FromString2(displayName);
                config.IsAdministrativelyDisabled = isAdministrativelyDisabled;
                config.MinProcesses = 0;
                config.MaxProcesses = 1;
                config.MaxClientsPerProcess = ServiceConfig.UnlimitedClientsPerProcess;
                config.MaxProcessAgeInSeconds = ServiceConfig.UnlimitedProcessAge;

                svmanager.SendCreateService(config);

                switch receive {
                    case svmanager.Ok():
                        Console.WriteLine("Service was successfully created.");
                        return 0;

                    case svmanager.RequestFailed(error):
                        Console.WriteLine("Failed to create service.");
                        SMSClient.ShowServiceError(error);
                        return -1;
                }

            }
            finally {
                delete svmanager;
            }
        }
    }

    [ConsoleCategory(Action="delete", HelpMessage="Delete an existing service")]
    internal class DeleteServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        reflective internal DeleteServiceCommand();

        internal int AppMain()
        {
            assert serviceName != null;
            if (serviceName.Length == 0) {
                Console.WriteLine("Invalid service name.");
                return -1;
            }

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {

                ServiceError error = SMSClient.SelectService(svmanager, serviceName);
                if (error != ServiceError.None)
                    return -1;

                svmanager.SendDeleteService();

                switch receive {
                    case svmanager.Ok():
                        Console.WriteLine("Service was successfully deleted.");
                        return 0;

                    case svmanager.RequestFailed(err):
                        Console.WriteLine("Failed to delete service.");
                        SMSClient.ShowServiceError(err);
                        return -1;
                }

            }
            finally {
                delete svmanager;
            }
        }
    }

    [ConsoleCategory(Action="enable", HelpMessage="Enable a service")]
    internal class EnableServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        reflective internal EnableServiceCommand();

        internal int AppMain()
        {
            assert serviceName != null;
            if (serviceName.Length == 0) {
                Console.WriteLine("Invalid service name.");
                return -1;
            }

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {

                ServiceError error = SMSClient.SelectService(svmanager, serviceName);
                if (error != ServiceError.None)
                    return -1;

                svmanager.SendEnableService(true);

                switch receive {
                    case svmanager.Ok():
                        Console.WriteLine("Service was successfully enabled.");
                        return 0;

                    case svmanager.RequestFailed(err):
                        Console.WriteLine("Failed to enable service.");
                        SMSClient.ShowServiceError(err);
                        return -1;
                }

            }
            finally {
                delete svmanager;
            }
        }
    }

    [ConsoleCategory(Action="disable", HelpMessage="Disable a service")]
    internal class DisableServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        reflective internal DisableServiceCommand();

        internal int AppMain()
        {
            assert serviceName != null;
            if (serviceName.Length == 0) {
                Console.WriteLine("Invalid service name.");
                return -1;
            }

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {

                ServiceError error = SMSClient.SelectService(svmanager, serviceName);
                if (error != ServiceError.None)
                    return -1;

                svmanager.SendEnableService(false);

                switch receive {
                    case svmanager.Ok():
                        Console.WriteLine("Service was successfully disabled.");
                        return 0;

                    case svmanager.RequestFailed(err):
                        Console.WriteLine("Failed to disable service.");
                        SMSClient.ShowServiceError(err);
                        return -1;
                }

            }
            finally {
                delete svmanager;
            }
        }
    }

    [ConsoleCategory(Action="kill", HelpMessage="Terminate the process(es) of a service.")]
    internal class TerminateServiceCommand
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter("service", Mandatory=true, Position=0)]
        internal string serviceName;

        [LongParameter("pid", Mandatory=false, Position=1, Default=-1)]
        internal long processId;

        reflective internal TerminateServiceCommand();

        internal int AppMain()
        {
            assert serviceName != null;
            if (serviceName.Length == 0) {
                Console.WriteLine("Invalid service name.");
                return -1;
            }

            ServiceManagerContract.Imp! svmanager = SMSClient.ConnectServiceManager();
            try {

                ServiceError error = SMSClient.SelectService(svmanager, serviceName);
                if (error != ServiceError.None)
                    return -1;

                if (processId != -1)
                    svmanager.SendTerminateServiceProcess((int)processId);
                else
                    svmanager.SendTerminateServiceAllProcesses();

                switch receive {
                    case svmanager.Ok():
                        return 0;

                    case svmanager.RequestFailed(err):
                        SMSClient.ShowServiceError(err);
                        return -1;
                }

            }
            finally {
                delete svmanager;
            }
        }
    }


    public class SMSClient
    {
        internal static ServiceManagerContract.Imp! ConnectServiceManager()
        {
            using (ImpatientWatcher watcher = new ImpatientWatcher("ConnectServiceManager", "create channel", 250)) {
                ErrorCode error;
                ServiceManagerContract.Imp! manager_imp;
                ServiceManagerContract.Exp! manager_exp;
                ServiceManagerContract.NewChannel(out manager_imp, out manager_exp);

                watcher.NextStep("NewClientEndpoint", 250);

                DirectoryServiceContract.Imp! rootds = DirectoryService.NewClientEndpoint();
                try {
                    watcher.NextStep("SdsUtils.Bind", 1000);
                    if (SdsUtils.Bind(ServiceManagerContract.ModuleName, rootds, manager_exp, out error)) {
                        watcher.NextStep("RecvSuccess", 250);
                        manager_imp.RecvSuccess();
                        return manager_imp;
                    }
                    else {
                        delete manager_imp;
                        Console.WriteLine("Failed to contact the Service Manager.  Error: " + SdsUtils.ErrorCodeToString(error));
                        throw new Exception("Failed to connect to Service Manager.");
                    }
                }
                finally {
                    delete rootds;
                }
            }
        }

        internal static ServiceError SelectService(ServiceManagerContract.Imp! svmanager, string! serviceName)
        {
            svmanager.SendSelectService(Bitter.FromString2(serviceName));
            switch receive {
                case svmanager.Ok():
                    // Console.WriteLine("Successfully selected service '{0}'.", serviceName);
                    return ServiceError.None;

                case svmanager.RequestFailed(error):
                    Console.WriteLine("Failed to select service '{0}'.", serviceName);
                    ShowServiceError(error);
                    return error;

                case svmanager.ChannelClosed():
                    throw new Exception("Service Manager closed channel before responding.");
            }
        }

        internal static void ShowServiceError(ServiceError error)
        {
            Console.WriteLine("ServiceError: " + ServiceEnums.ToString(error));
        }

        static internal int StartService(string! serviceName, bool wait)
        {
            ServiceManagerContract.Imp! svmanager = ConnectServiceManager();

            try {

                ServiceError error = SelectService(svmanager, serviceName);
                if (error != ServiceError.None) {
                    return -1;
                }

                if (wait) {
                    svmanager.SendStartServiceWait();

                    for (;;) {
                        switch receive {
                            case svmanager.RequestFailed(err):
                                ShowServiceError(err);
                                return -1;

                            case svmanager.ServiceStarting():
                                Console.WriteLine("Service Manager accepted request to start service '{0}'.", serviceName);
                                return 0;

                            case timeout(TimeSpan.FromSeconds(10)):
                                Console.WriteLine("waiting...");
                                break;
                        }
                    }
                }
                else {
                    svmanager.SendStartServiceNoWait();

                    switch receive {
                        case svmanager.RequestFailed(err):
                            ShowServiceError(err);
                            return -1;

                        case svmanager.ServiceStarting():
                            Console.WriteLine("Service Manager accepted request to start service '{0}'.", serviceName);
                            return 0;
                    }
                }
            }
            finally {
                delete svmanager;
            }
        }

        internal static int StopService(string! serviceName, bool wait)
        {
            ServiceManagerContract.Imp! svmanager = ConnectServiceManager();

            try {

                ServiceError error = SelectService(svmanager, serviceName);
                if (error != ServiceError.None)
                    return -1;

                if (wait) {
                    svmanager.SendStopServiceWait();

                    for (;;) {
                        switch receive {
                            case svmanager.RequestFailed(err):
                                ShowServiceError(err);
                                if (err == ServiceError.CannotStopService) {
                                    Console.WriteLine("If this service is an 'always active' service, then the stop command cannot be used.");
                                    Console.WriteLine("Instead, use the 'disable' command.");
                                }
                                return -1;

                            case svmanager.ServiceStopping():
                                Console.WriteLine("Service Manager accepted request to stop service '{0}'.", serviceName);
                                return 0;

                            case timeout(TimeSpan.FromSeconds(10)):
                                Console.WriteLine("waiting...");
                                break;
                        }
                    }
                }
                else {
                    svmanager.SendStopServiceNoWait();

                    switch receive {
                        case svmanager.RequestFailed(err):
                            ShowServiceError(err);
                            return -1;

                        case svmanager.ServiceStopping():
                            Console.WriteLine("Service Manager accepted request to stop service '{0}'.", serviceName);
                            return 0;
                    }
                }
            }
            finally {
                delete svmanager;
            }
        }

        internal static int WatchService(string! serviceName)
        {
            ServiceManagerContract.Imp! svmanager = ConnectServiceManager();

            try {

                ServiceError error = SelectService(svmanager, serviceName);
                if (error != ServiceError.None) {
                    return -1;
                }

                svmanager.SendWatchServiceStatus();

                switch receive {
                    case svmanager.RequestFailed(err):
                        ShowServiceError(err);
                        return -1;

                    case svmanager.Ok():
                        Console.WriteLine("Service Manager accepted request to watch service '{0}'.", serviceName);
                        break;
                }

                for (;;) {
                    svmanager.SendWaitServiceChange();

                    switch receive {
                        case svmanager.ServiceStatusChanged(ServiceStatus status, bool missedChange):
                            Console.WriteLine("Status changed: ");
                            Console.WriteLine("    State:   " + ServiceEnums.ToString(status.State));
                            if (missedChange) {
                                Console.WriteLine("    Note: At least one status change was missed.");
                            }
                            break;

                        case svmanager.RequestFailed(err):
                            Console.WriteLine("Request failed.");
                            ShowServiceError(err);
                            return -1;

                        case svmanager.ChannelClosed():
                            Console.WriteLine("Service Manager closed channel!");
                            return -1;
                    }
                }

            }
            finally {
                delete svmanager;
            }
        }

        const string ListServiceFormat = "{0,-20} {1,-10} {2,-6} {3}";

        internal static int ListServices(ListConfig! config)
        {
            ServiceManagerContract.Imp! svmanager = ConnectServiceManager();


            try {
                Console.WriteLine(ListServiceFormat, "Name", "State", "PID", "Display Name");
                Console.WriteLine(ListServiceFormat,
                    new String('-', 20),
                    new String('-', 10),
                    new String('-', 6),
                    new String('-', 30));

                ServiceInfo[]! in ExHeap first_entries = new[ExHeap] ServiceInfo[40];
                svmanager.SendEnumerateServices(first_entries);

                for (;;) {
                    switch receive {
                        case svmanager.EnumerationTerminated(entries, count):
                            ListServices(entries, count);
                            delete entries;
                            return 0;

                        case svmanager.NextServiceInfo(entries, count):
                            ListServices(entries, count);
                            svmanager.SendEnumerateServices(entries);
                            break;

                        case svmanager.ChannelClosed():
                            Console.WriteLine("Service Manager channel closed");
                            return -1;

                    }
                }
            }
            finally {
                delete svmanager;
            }
        }

        static void ListServices(ServiceInfo[]! in ExHeap entries, int count)
        {
            for (int i = 0; i < count; i++) {
                expose(entries[i])
                {
                    string! serviceName = ToString(entries[i].Config.ServiceName);
                    string! displayName = ToString(entries[i].Config.DisplayName);
                    string! stateString = ServiceEnums.ToString(entries[i].Status.State);
                    string! processIdString = entries[i].Status.ProcessId != -1 ?
                        (!)entries[i].Status.ProcessId.ToString() : "";
                    Console.WriteLine(ListServiceFormat, serviceName, stateString, processIdString, displayName);
                }
            }
        }

        public static string! ToString(char[] in ExHeap str)
        {
            if (str != null)
                return Bitter.ToString2(str);
            else
                return "";
        }

        public static void ShowConfigDetailed(ServiceConfig config)
        {
            if (config.ServiceName == null) {
                Console.WriteLine("Error: A ServiceConfig structure had a null ServiceName field.");
                return;
            }
            string! serviceName = Bitter.ToString2(config.ServiceName);

            string! executableName = config.ExecutableName != null ? Bitter.ToString2(config.ExecutableName) : "";
            string! displayName = config.DisplayName != null ? Bitter.ToString2(config.DisplayName) : "";

            Console.WriteLine("Service Configuration");
            Console.WriteLine("---------------------");
            Console.WriteLine();
            Console.WriteLine(DetailFormat, "Service Name", serviceName);
            Console.WriteLine(DetailFormat, "Executable", executableName);
            Console.WriteLine(DetailFormat, "Display Name", displayName);
            Console.WriteLine(DetailFormat, "Activation Mode", ServiceEnums.ToString(config.ActivationMode));
            Console.WriteLine(DetailFormat, "Is Disabled?", config.IsAdministrativelyDisabled.ToString());

            Console.WriteLine(DetailFormat, "Min/Max Processes", String.Format("min {0} / {1}",
                config.MinProcesses,
                config.MaxProcesses == ServiceConfig.UnlimitedProcesses ? "no max" : "max " + config.MaxProcesses));

            string! max_age_text;
            if (config.MaxProcessAgeInSeconds == ServiceConfig.UnlimitedProcessAge)
                max_age_text = "unlimited";
            else {
                TimeSpan limit = TimeSpan.FromSeconds(config.MaxProcessAgeInSeconds);
                max_age_text = (!)limit.ToString();
            }
            Console.WriteLine(DetailFormat, "Max Process Age", max_age_text);

            string clients_per_process_text;
            if (config.MaxClientsPerProcess == ServiceConfig.UnlimitedClientsPerProcess) {
                clients_per_process_text = "unlimited";
            }
            else {
                clients_per_process_text = config.MaxClientsPerProcess.ToString();
            }
            Console.WriteLine(DetailFormat, "Max Clients per Process", clients_per_process_text);

        }

        const string DetailFormat = "{0,-25}: {1}";

        public static void ShowStatusDetailed(ServiceStatus status)
        {
            Console.WriteLine("Service Status");
            Console.WriteLine("--------------");
            Console.WriteLine();
            Console.WriteLine(DetailFormat, "State", ServiceEnums.ToString(status.State));
            if (status.State != ServiceState.Stopped) {
                Console.WriteLine(DetailFormat, "Process ID", status.ProcessId);
            }

            // This is not yet accurate.
            // Console.WriteLine(DetailFormat, "Total Active Clients", status.TotalActiveClients);

            Console.WriteLine(DetailFormat, "Total Active Processes", status.TotalActiveProcesses);
            Console.WriteLine(DetailFormat, "Connect Queue Length", status.ConnectQueueLength);

            Console.WriteLine(DetailFormat, "Last Process Start", status.LastStartFailed ? "FAILED" : "Succeeded");
            if (status.LastStartFailed) {
                Console.WriteLine(DetailFormat, "Last Start Error", ServiceEnums.ToString(status.LastStartError));
            }
        }
    }

}

