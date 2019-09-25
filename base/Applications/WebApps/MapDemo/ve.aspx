<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=windows-1252">
<meta http-equiv="Pragma" content="no-cache">
<meta http-equiv="Expires" content="-1">

<title>Caffeinate me!</title>

<style type="text/css">
div.whiteBox
{
  color: black;
  border: solid;
  padding: 10px 10px 10px 10px;
  background-color: white;
}
.pinText
{
  width:44px;height:17px;
  font-family:Arial,sans-serif;
  font-weight:bold;font-size:8pt;
  color:White;overflow:hidden;
  cursor:pointer;text-decoration:none;
  text-align:center;background:#0000FF;
  border:1px solid #FFFFFF;
  z-index:5
}
.pinIcon
{
  font-family:Arial,sans-serif;
  font-weight:bold;font-size:8pt;
  color:White;overflow:hidden;
  cursor:pointer;text-decoration:none;
  text-align:center;background:#0000FF;
  z-index:5
}
.pinRed
{
  width:44px;height:17px;
  font-family:Arial,sans-serif;
  font-weight:bold;font-size:8pt;
  color:White;overflow:hidden;
  cursor:pointer;text-decoration:none;
  text-align:center;background:#FF0000;
  border:1px solid #000000;
  z-index:5
}
.pinGreen
{
  width:44px;height:17px;
  font-family:Arial,sans-serif;
  font-weight:bold;font-size:8pt;
  color:White;overflow:hidden;
  cursor:pointer;text-decoration:none;
  text-align:center;background:#00F000;
  border:1px solid #000000;
  z-index:5
}
</style>

<link href="http://dev.virtualearth.net/standard/v2/MapControl.css" type="text/css" rel="stylesheet" />
<script src="http://dev.virtualearth.net/standard/v2/MapControl.js">
</script>

<script src='LocalSearch.js?loc=<%=Request.QueryString("loc")%>&search=<%=Request.QueryString("search")%>'></script>

<script src='Traffic.js?loc=<%=Request.QueryString("loc")%>'></script>

<script>
    var map = null;
    function OnPageLoad()
    {
                // Default to Seattle if no location is specified
                var latLoc = 47.62786; // North
                var longLoc = -122.31145; // West
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
                AddSearchResultsPushpins(map);
                AddTrafficResultsPushpins(map);
        }
</script>
</head>

<body BGCOLOR="#747170" TEXT="#FFFFFF" vlink="0000FF" alink="0000FF" link="0000FF" onload="OnPageLoad()">
<h1 align="center">In Search of Caffeine</h1>
<table cellpadding="10" cellspacing="5" border="0">
<tr>
<td valign=top>
        <div class="whiteBox">
        Locations:
        <br>&gt;<a href="ve.aspx?loc=redmond&search=<%=Request.QueryString("search")%>">Redmond / Microsoft</a>
        <br>&gt;<a href="ve.aspx?loc=seattle&search=<%=Request.QueryString("search")%>">Seattle / Home</a>
        <p></p>
        Coffee:
        <br><img src="green.bmp"> <a href="ve.aspx?loc=<%=Request.QueryString("loc")%>&search=starbucks">Starbucks</a>
        <br><img src="red.bmp"> <a href="ve.aspx?loc=<%=Request.QueryString("loc")%>&search=tullys">Tully's</a>
        <br><a href="ve.aspx?loc=<%=Request.QueryString("loc")%>&search=all">All chains</a>
        <p></p>
        Traffic:
        <br><div class="pinRed">Heavy</div>
        <br><div class="pinGreen">Light</div>
        <p></p>
        </div>
</td>
<td>
        <div id="myMap" style="WIDTH: 600px; HEIGHT: 400px; OVERFLOW:hidden"></div>
</td>
</tr>
</table>
</body>
</html>
