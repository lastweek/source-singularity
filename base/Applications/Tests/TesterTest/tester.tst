<Profile Name="Sample">
  <Module Name="TestDriver">
    <Suite Name="SampleTest">
       <Test Name="HelloTest"/>
       <Test Name="ClassInitTest"/>
       <Test Name="EqualTest"/>
    </Suite>
    <Suite Name="FailTest">
       <Test Name="SkipTest"/>
       <Test Name="TimeoutTest" Timeout="10" KnownFailure="Test should fail with timeout"/>
       <Test Name="UnknownTest" KnownFailure="Test should fail because it does not exist"/>
    </Suite>
  </Module>
</Profile>
