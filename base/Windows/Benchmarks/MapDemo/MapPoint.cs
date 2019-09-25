// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;

using mapdemo.MapPointService;

namespace MapPointNamespace
{
	public class MapPoint
	{
		const string mpwsUserName = "7356";
		const string mpwsPassword = "0[[{NmN?UU5?U";
		private static bool initialized = false;
		public static RenderServiceSoap renderService = null;

		public MapPoint()
		{
			// Nada
		}

		public static bool Initialized
		{
			get { return initialized; }
		}

		public static void Initialize()
		{
			// Render service
			renderService = new RenderServiceSoap();
			renderService.Credentials = new System.Net.NetworkCredential(mpwsUserName, mpwsPassword);
			renderService.PreAuthenticate = true;

			initialized = true;
		}

		public static MapSpecification PrepareMapFromCenterZoom(
			int widthPixels, int heightPixels,
			double centerLatitude, double centerLongitude,
			double zoom)
		{
			// Options
			MapOptions mapOptions = new MapOptions();
			mapOptions.ReturnType = MapReturnType.ReturnImage;
			mapOptions.Format = new ImageFormat();
			mapOptions.Format.Width = widthPixels;
			mapOptions.Format.Height = heightPixels;
			mapOptions.Format.MimeType = "image/gif";
			mapOptions.Zoom = zoom;

			// View
			ViewByScale[] viewByScaleArray = new ViewByScale[1];
			viewByScaleArray[0] = new ViewByScale();
			viewByScaleArray[0].CenterPoint = new LatLong();
			viewByScaleArray[0].CenterPoint.Latitude = centerLatitude;
			viewByScaleArray[0].CenterPoint.Longitude = centerLongitude;
			viewByScaleArray[0].MapScale = 1.0;

			// Specifications
			MapSpecification mapSpecification = new MapSpecification();
			mapSpecification.Options = mapOptions;
			mapSpecification.Views = viewByScaleArray;
			mapSpecification.DataSourceName = "MapPoint.NA";

			return mapSpecification;
		}

		public static byte[] GetMap(MapSpecification map)
		{
			// Declare the map image array and get the map
			MapImage[] mapImageArray = null;

			try
			{
				mapImageArray = renderService.GetMap(map);
			}
			catch (System.Net.WebException) {
				// Better error handling?
				return null;
			}

			// Careful return
			if (null != mapImageArray && null != mapImageArray[0])
			{
				return mapImageArray[0].MimeData.Bits;
			}
			else {
				return null;
			}
		}
	}
}
