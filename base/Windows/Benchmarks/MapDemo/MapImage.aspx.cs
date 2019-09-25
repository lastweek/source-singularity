// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Web;

using mapdemo.MapPointService;
using MapPointNamespace;

namespace mapdemo
{
	/// <summary>
	/// Summary description for WebForm1.
	/// </summary>
	public class MapImage : System.Web.UI.Page
	{
		private const int mapWidth = 400;
		private const int mapHeight = 500;

		private void Page_Load(object sender, System.EventArgs e)
		{
			// Put user code to initialize the page here
		}

		protected void ServeMap()
		{
			if (!MapPointNamespace.MapPoint.Initialized)
			{
				MapPointNamespace.MapPoint.Initialize();
			}

			bool isSeattle = true; // default to Seattle
			double centerLat, centerLong, zoom;

			if ((Request.QueryString["city"] != null) &&
				(Request.QueryString["city"].ToLower().Equals("redmond")))
			{
				isSeattle = false;
			}

			byte mask = 0xff;

			if (Request.QueryString["mask"] != null)
			{
				try
				{ mask = Byte.Parse(Request.QueryString["mask"]); }
				catch (Exception) { /* ignore */ }
			}

			if (!isSeattle)
			{
				centerLat = redmondCenterLat;
				centerLong = redmondCenterLong;
				zoom = redmondZoom;
			}
			else {
				centerLat = seattleCenterLat;
				centerLong = seattleCenterLong;
				zoom = seattleZoom; 
			}

			try
			{
				MapSpecification spec = MapPointNamespace.MapPoint.PrepareMapFromCenterZoom(
					mapWidth, mapHeight, centerLat, centerLong, zoom);

				// Add pushpins to the map specification!
				if (isSeattle)
				{
					spec.Pushpins = BuildPushPins(SeattlePushPins, mask);
				}
				else {
					spec.Pushpins = BuildPushPins(RedmondPushPins, mask);;
				}
				
				// Fetch the map image;
				byte[] data = MapPointNamespace.MapPoint.GetMap(spec);

				if (data == null)
				{
					Response.StatusCode = 500;
					Response.StatusDescription = "Failed to retrieve map data";
				}
				else {
					Response.ContentType= "image/gif";
					Response.BinaryWrite(data);
				}
			}
			catch (Exception ex) {
				Response.Write(ex);
				return;
			}
		}

		private mapdemo.MapPointService.Pushpin[] BuildPushPins(PushPinData[] pins, byte mask)
		{
			// First count how many pins are going to match the mask
			int numPins = 0;
			for (int i = 0; i < pins.Length; ++i)
			{
				if ((pins[i].groupMask == 0) || ((pins[i].groupMask & mask) != 0))
				{
					numPins++;
				}
			}

			mapdemo.MapPointService.Pushpin[] specPins = new mapdemo.MapPointService.Pushpin[numPins];

			int outputIndex = 0;
			for (int i = 0; i < pins.Length; ++i)
			{
				if ((pins[i].groupMask == 0) || ((pins[i].groupMask & mask) != 0))
				{
					specPins[outputIndex] = new mapdemo.MapPointService.Pushpin();
					specPins[outputIndex].LatLong = new mapdemo.MapPointService.LatLong();

					specPins[outputIndex].IconDataSource = "MapPoint.Icons";
					specPins[outputIndex].IconName = pins[i].icon;
					specPins[outputIndex].Label = pins[i].label;
					specPins[outputIndex].LabelNearbyRoads = false;
					specPins[outputIndex].LatLong.Latitude = pins[i].latitude;
					specPins[outputIndex].LatLong.Longitude = pins[i].longitude;
					specPins[outputIndex].ReturnsHotArea = false;
					++outputIndex;
				}
			}

			return specPins;
		}

		private const double seattleCenterLat = 47.616391194232195;
		private const double seattleCenterLong = -122.32471226177632;
		private const double seattleZoom = 7;

		private const double redmondCenterLat = 47.664037990827104;
		private const double redmondCenterLong = -122.12025798221626;
		private const double redmondZoom = 10;

		private struct PushPinData
		{
			public double latitude;
			public double longitude;
			public string icon;
			public string label;
			public byte groupMask;

			public PushPinData(double latit, double longi, string ic,
				string lab, byte mask)
			{
				latitude = latit;
				longitude = longi;
				icon = ic;
				label = lab;
				groupMask = mask;
			}
		}

		private static readonly PushPinData[] RedmondPushPins = {
			// "You are here"
			new PushPinData(47.641372008066419, -122.14171843658843, "42" /*office building*/, "You are here (Microsoft Research)", 0),
			// Starbucks
			new PushPinData(47.681110048657551, -122.12546258636381, "DriveThruIcon" /*green coffee circle*/, null, 1),
			new PushPinData(47.674440368933034, -122.12920553002897, "DriveThruIcon", null, 1),
			new PushPinData(47.674293519865877, -122.12964266213585, "DriveThruIcon", null, 1),
			new PushPinData(47.670646198849091, -122.1135097553162,  "DriveThruIcon",  null, 1),
			new PushPinData(47.670878425280875, -122.11128311364686, "DriveThruIcon", null, 1),
			new PushPinData(47.671243840401466, -122.10595556609425, "DriveThruIcon", null, 1),
			new PushPinData(47.652327631495119, -122.13483360590506, "DriveThruIcon", null, 1),
			// Tullys
			new PushPinData(47.6810758977117,   -122.12546258636381, "CoffeeShopIcon" /*Red coffee circle*/, null, 2),
			new PushPinData(47.671001368685936, -122.04650559955846, "CoffeeShopIcon", null, 2),
			// SBC
			new PushPinData(47.670178330890948, -122.11961594443427, "KioskIcon" /*Blue coffee circle*/, null, 4),
			new PushPinData(47.608457326456126, -122.20149625220438, "KioskIcon", null, 4),
			new PushPinData(47.574152701349739, -122.17140243872132, "KioskIcon", null, 4)
		};

		private static readonly PushPinData[] SeattlePushPins = {
			// "You are here"
			new PushPinData(47.614037591008028, -122.30879852406528, "27" /*house with flag*/, "You are here (home)", 0),
			// Starbucks
			new PushPinData(47.556308832143081, -122.14664983316918, "DriveThruIcon" /*green coffee circle*/, null, 1),
			new PushPinData(47.609201817075657, -122.31668056236748, "DriveThruIcon", null, 1),
			new PushPinData(47.619942289545506, -122.31374358102437, "DriveThruIcon", null, 1),
			new PushPinData(47.599257061644117, -122.30209127830034, "DriveThruIcon", null, 1),
			new PushPinData(47.621212704731128, -122.31263709037883, "DriveThruIcon", null, 1),
			new PushPinData(47.612890119227465, -122.32072403435613, "DriveThruIcon", null, 1),
			new PushPinData(47.601862778812482, -122.28519339029373, "DriveThruIcon", null, 1),
			new PushPinData(47.6102400058295,   -122.32292335526887, "DriveThruIcon", null, 1),
			new PushPinData(47.556308832143081, -122.14664983316918, "DriveThruIcon", null, 1),
			new PushPinData(47.622145025552832, -122.32086063813952, "DriveThruIcon", null, 1),
			new PushPinData(47.622367006700856, -122.32081965700451, "DriveThruIcon", null, 1),
			new PushPinData(47.618466968684778, -122.32557346866683, "DriveThruIcon", null, 1),
			new PushPinData(47.616233496826183, -122.32989014822229, "DriveThruIcon", null, 1),
			new PushPinData(47.617053119526588, -122.33032728032917, "DriveThruIcon", null, 1),
			// Tullys
			new PushPinData(47.556308832143081, -122.14664983316918, "137", null, 6),
			new PushPinData(47.626021157906813, -122.30730954282622, "CoffeeShopIcon", null, 2),
			new PushPinData(47.607811873579557, -122.33913822435848, "CoffeeShopIcon", null, 2),
			new PushPinData(47.556308832143081, -122.14664983316918, "CoffeeShopIcon", null, 2),
			new PushPinData(47.617097515756193, -122.35281226307684, "CoffeeShopIcon", null, 2),
			new PushPinData(47.605650118707253, -122.33404290323766, "CoffeeShopIcon", null, 2),
			new PushPinData(47.60911643971103,  -122.33572312977347, "137", null, 6),
			new PushPinData(47.608771515157947, -122.34009445084229, "137", null, 6),
			new PushPinData(47.599181929563251, -122.33139278983968, "137", null, 6),
			new PushPinData(47.633845139601064, -122.28094501262997, "CoffeeShopIcon", null, 2),
			new PushPinData(47.556308832143081, -122.14664983316918, "137", null, 6),
			new PushPinData(47.610117062424443, -122.33346916734737, "CoffeeShopIcon", null, 2),
			new PushPinData(47.611677760649791, -122.33647445058217, "CoffeeShopIcon", null, 2),
			// SBC
			new PushPinData(47.610117062424443, -122.33655641285222, "KioskIcon", /*Blue coffee circle*/ null, 4),
			new PushPinData(47.60678051501489,  -122.33355112961741, "KioskIcon", null, 8),
			new PushPinData(47.602412609040663, -122.33254026162025, "KioskIcon", null, 8),
			new PushPinData(47.608826156671306, -122.33998516781557, "KioskIcon", null, 8),
			new PushPinData(47.556308832143081, -122.14664983316918, "KioskIcon", null, 8)
		};

		#region Web Form Designer generated code
		override protected void OnInit(EventArgs e)
		{
			//
			// CODEGEN: This call is required by the ASP.NET Web Form Designer.
			//
			InitializeComponent();
			base.OnInit(e);
		}
		
		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent()
		{    
			this.Load += new System.EventHandler(this.Page_Load);
		}
		#endregion
	}
}
