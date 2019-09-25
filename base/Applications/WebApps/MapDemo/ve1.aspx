<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=windows-1252">
<meta http-equiv="Pragma" content="no-cache">
<meta http-equiv="Expires" content="-1">

<title>VE Demo 1</title>

<style type="text/css">
div.whiteBox
{
  color: black;
  border: solid;
  padding: 10px 10px 10px 10px;
  background-color: white;
}
.pin
{
  width:44px;height:17px;
  font-family:Arial,sans-serif;
  font-weight:bold;font-size:8pt;
  color:White;overflow:hidden;
  cursor:pointer;text-decoration:none;
  text-align:center;background:#0000FF;
  border:1px solid #000000;
  z-index:5
}
</style>

<!-- script src="MapControl.js"></script -->
<link href="http://dev.virtualearth.net/standard/v2/MapControl.css" type="text/css" rel="stylesheet" />
<script src="http://dev.virtualearth.net/standard/v2/MapControl.js">
</script>

<script>
    var map = null;
    function OnPageLoad()
    {
                // Default to Seattle if no location is specified
                var latLoc = 47.63954; // North
                var longLoc = -122.31706; // West
                var zoomLoc = 14;
                var nameLoc = "Home";
                var queryString = window.location.search.substring(1);
                if (queryString.indexOf("loc=redmond") != -1)
                {
                        latLoc = 47.64187; // North
                        longLoc = -122.14207; // West
                        zoomLoc = 13;
                        nameLoc = "MSR";
                }

                var params = new Object();
                params.latitude  = latLoc;
                params.longitude = longLoc;
                params.zoomlevel = zoomLoc;
                params.mapstyle  = Msn.VE.MapStyle.Road;
                params.showScaleBar = true;
                params.showDashboard = true;
                params.dashboardSize = Msn.VE.DashboardSize.Normal;
                params.dashboardX = 3;
                params.dashboardY = 3;

                // Create the Virtual Earth control, add a pushpin, and render it in a div element
                map = new Msn.VE.MapControl(document.getElementById("myMap"), params);
                map.Init();

                map.AddPushpin('pin1', latLoc, longLoc, 0, 0, 'pinText', nameLoc, 0);
        }
</script>
</head>

<body BGCOLOR="#747170" TEXT="#FFFFFF" vlink="0000FF" alink="0000FF" link="0000FF" onload="OnPageLoad()">
<h2>VE Demo 1 - Virtual Earth Hosting</h2>
<table cellpadding="10" cellspacing="5" border="0">
<tr>
<td valign=top>
        <div class="whiteBox">
        Locations:
        <br>&gt; <a href="ve1.aspx?loc=redmond">Redmond / Microsoft</a>
        <br>&gt; <a href="ve1.aspx?loc=seattle">Seattle / Home</a>
        <p></p>
        <br> <a href="ve2.aspx">Next demo</a>
        </div>
</td>
<td>
        <div id="myMap" style="WIDTH: 600px; HEIGHT: 400px; OVERFLOW:hidden"></div>
</td>
</tr>
</table>
</body>
</html>
