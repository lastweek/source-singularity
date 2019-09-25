using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class tracking_ilgen: ilgen {
	public Tracking tracking;

	public Tracking create(compilation_unit c) {
		this.compilation_unit(c);
		return tracking;
	}

	public tracking_ilgen(Tracking w, compilation_unit c) : base(w, c) {
		tracking = w;
	}
}
