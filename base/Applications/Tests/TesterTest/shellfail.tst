<Profile Name="Sample">
  <Module Name="TestDriver">
    <Suite Name="ShellX" KnownFailure="These don't work right now or throw a deliberate exception">
       <Test Name="pnp"/>
       <Test Name="disk"/>
       <Test Name="warmboot"/>
       <Test Name="play"/>
       <Test Name="throw"/>
       <Test Name="throwwithlinkstack"/>
    </Suite>
  </Module>
</Profile>
