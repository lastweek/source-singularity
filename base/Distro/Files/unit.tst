<?xml version="1.0"?>
<!--Export of test type unit-->
<!--GENERATED FILE. DO NOT EDIT. Add test cases via Product Studio, according to SDN 51-->
<Profile Name="unit">
    <Module Name="EventTest">
        <Suite Name="EventTest">
            <Test Name="TestPermStack1M" />
            <Test Name="TestRecNoStack4" />
            <Test Name="TestRecStack64" />
        </Suite>
    </Module>
    <Module Name="FibTest">
        <Suite Name="FibTest">
            <Test Name="StealTest" />
        </Suite>
    </Module>
    <Module Name="InsightTests">
        <Suite Name="DependencyObjectCollectionTests">
            <Test Name="AddTest" />
            <Test Name="ClearTest" />
            <Test Name="InsertTest" />
            <Test Name="OnPropertyChangedTest" />
            <Test Name="RemoveAtTest" />
            <Test Name="RemoveTest" />
            <Test Name="SetValueTest" />
        </Suite>
        <Suite Name="DependencyObjectTests">
            <Test Name="AttachedPropertyTest" />
            <Test Name="DefaultValueTest" />
            <Test Name="IllegalPropertyTypeTest" />
            <Test Name="IllegalSetValueTest" />
            <Test Name="OnPropertyChangedTest" />
            <Test Name="SetValueTest" />
        </Suite>
        <Suite Name="ObserverFrameworkTests">
            <Test Name="LoadObserverTree" />
        </Suite>
    </Module>
    <Module Name="MonitorTest">
        <Suite Name="PulseAllTest">
            <Test Name="FewThreadsTest" Timeout="180000" />
            <Test Name="ManyThreadsTest" Timeout="180000" />
        </Suite>
        <Suite Name="PulseTest">
            <Test Name="HighDensityTest" Timeout="180000" />
            <Test Name="LowDensityTest" Timeout="180000" />
            <Test Name="MediumDensityTest" Timeout="180000" />
        </Suite>
    </Module>
    <Module Name="PromiseTest">
        <Suite Name="TodoTest">
            <Test Name="AsyncMessage" />
            <Test Name="BlockedQueue" />
            <Test Name="MultiQueue" />
            <Test Name="RunDirect" />
            <Test Name="RunInQueue" />
            <Test Name="SimplePromise" />
        </Suite>
    </Module>
    <Module Name="TestDriver">
        <Suite Name="FailTest">
            <Test Name="SkipTest" KnownFailure="This test is supposed to automatically be skipped" />
            <Test Name="TimeoutTest" Timeout="10" KnownFailure="Timeout" />
            <Test Name="UnknownTest" KnownFailure="This is a profile entry with no associated test" />
        </Suite>
        <Suite Name="SampleTest">
            <Test Name="ClassInitTest" />
            <Test Name="EqualTest" />
            <Test Name="HelloTest" />
        </Suite>
        <Suite Name="Shell">
            <Test Name="channeldemo" />
            <Test Name="dir /init" />
            <Test Name="iotestapp -count=10000" />
            <Test Name="memstress -sip_oom" KnownFailure="This is currently non-functional on PAGING builds (PS 510)" />
            <Test Name="select" />
            <Test Name="singbench" Timeout="180000" />
            <Test Name="tasklist" />
            <Test Name="threadtest" />
            <Test Name="throw" />
            <Test Name="throwwithlinkstack" />
        </Suite>
    </Module>
    <Module Name="Threading">
        <Suite Name="ThreadingTest">
            <Test Name="AutoResetEventTest" />
            <Test Name="ManualResetEventTest" />
            <Test Name="MutexTest" />
            <Test Name="SyncTest" />
            <Test Name="WaitAnyTest" />
        </Suite>
    </Module>
</Profile>